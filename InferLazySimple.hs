{-# LANGUAGE LambdaCase #-}
import Prelude hiding (flip)
import Data.List
import Data.Functor
-- import Data.Set as Set

import Debug.Trace
import GHC.Exts (Constraint)
import qualified Data.IntSet as Oset

{- A lazy subtyping algorithm:

A,B := a | ^a | Int | A -> B | forall a. A | 
T ::= . | T,a | T,^a | T, lbs <: ^a <: ubs |- A <: B

Algorithm:

01. T, a                               --> T                                                      (rule 1)
02. T[^a] |- [l1..ln] <: ^a <:[u1..um] --> T |- l1 <: u1 .... |- ln <: lm (n x m)                 (rule 2)
03. T |- Int <: Int                    --> T                                                      (rule 5)
04. T[a]  |- a <: a                    --> T                                                      (rule 6)
05. T[^a] |- ^a <: ^a                  --> T                                                      (rule 7)


06. T |- A -> B <: C -> D              --> T |- C <: A |- B <: D                                  (rule 8)
07. T |- forall a . B <: C             --> T,^a |- [^a/a] B <: C                                  (rule 9)
08. T |- A <: forall b . B             --> T,b |- A <: C                                          (rule 10)


09. T[lbs <: ^a < ubs] |- ^a <: A -> B --> T[^a1,^a2, lbs <: ^a < ubs U {^a1,^a2}] |- ^a1 -> ^a2 <: A -> B  
          when not monotype (A->B)  
10. T[lbs <: ^a < ubs] |- A -> B <: ^a --> T[^a1,^a2, lbs U {^a1,^a2} <: ^a < ubs] |- A -> B <: ^a1 -> ^a2   
          when not monotype (A->B)  

11. T[a][lbs <: ^b < ubs] |- a <: ^b   --> T[a][lbs U {a} <: ^b < ub] 
12. T[a][lbs <: ^b < ubs] |- ^b <: a   --> T[a][lbs <: ^b < ub U {a}] 
13. T[lbs <: ^b < ubs] |- Int <: ^b    --> T[a][lbs U {Int} <: ^b < ub] 
14. T[lbs <: ^b < ubs] |- ^b <: Int    --> T[a][lb s<: ^b < ub U {Int}] 

15. T[^a][lbs <: ^b < ubs] |- ^a <: ^b --> T[^a][lb U {^a} <: ^b < ub] 
16. T[^a][lbs <: ^b < ubs] |- ^b <: ^a --> T[^a][lb <: ^b < ub U {^a}] 


--------------
[A/^a]_E T
--------------

[A/^a]_E (T,^a)             = T,E                 ^a notin fv(A)
[A/^a]_E (T,^b)             = [A/^a]_E T,^b       ^b notin FV(A)
[A/^a]_E (T,^b)             = [A/^a]_{E,^b} T     ^b in FV(A)
[A/^a]_E (T |- B <: C)      = [A/^a]_E T |- [A/^a] B <: [A/^a] C

-}

data Typ = TVar (Either Int Int) | TInt | TForall (Typ -> Typ) | TArrow Typ Typ

-- Consider changing to set
data Work = WVar Int | WExVar Int [Typ] [Typ] | Sub Typ Typ deriving Eq

data Bound = LB | UB

ppTyp :: Int -> Typ -> String
ppTyp n (TVar (Left i))  = show i
ppTyp n (TVar (Right i)) = "^" ++ show i
ppTyp n TInt             = "Int"
ppTyp n (TArrow a b)     = "(" ++ ppTyp n a ++ ") -> " ++ ppTyp n b
ppTyp n (TForall f)      = "forall " ++ show n ++ ". " ++ ppTyp (n+1) (f (TVar (Left n)))

eqTyp :: Int -> Typ -> Typ -> Bool
eqTyp n TInt TInt = True
eqTyp n (TVar v1) (TVar v2)  = v1 == v2
eqTyp n (TArrow a b) (TArrow c d) = a == c && b == d
eqTyp n (TForall g) (TForall h) = eqTyp (n+1) (g (TVar (Left n))) (h (TVar (Left n)))
eqTyp n _ _ = False

instance Show Typ where
  show = ppTyp 0

instance Show Work where
  show (WVar i)   = show i
  show (WExVar i lbs ubs)  = show lbs ++ " <: " ++ "^" ++ show i ++ " <: " ++ show ubs
  show (Sub a b)      = show a ++ " <: " ++ show b

instance Eq Typ where
  t1 == t2 = eqTyp 0 t1 t2

mono :: Typ -> Bool
mono (TForall g)  = False
mono (TArrow a b) = mono a && mono b
mono _            = True

fv :: Typ -> [Typ]
fv (TVar (Right i)) = [TVar (Right i)]
fv (TArrow t1 t2)   = fv t1 `union` fv t2
fv (TForall g)      = fv (g TInt)
fv _                = []

wsToVars :: [Work] -> [Either Int Int]
wsToVars = concatMap (\case
                        WVar i -> [Left i]
                        WExVar i _ _ -> [Right i]
                        _ -> []
                     )

fvInBounds :: [Typ] -> [Typ] -> [Typ]
fvInBounds lbs ubs = nub (concatMap fv lbs ++ concatMap fv ubs)

fvInVarBounds :: [Work] -> Typ -> [Typ]
fvInVarBounds ws var = case getWorkFromExTyp ws var of
                         (WExVar _ lbs ubs) -> fvInBounds lbs ubs
                         _ -> error "Impossible"

getVarsBeforeTyp :: [Work] -> Typ -> [Typ]
getVarsBeforeTyp ws (TVar i) = map TVar $ dropWhile (/= i) $ wsToVars ws
getVarsBeforeTyp ws x = error (show x ++ "is not a type")

getVarsAfterTyp :: [Work] -> Typ -> [Typ]
getVarsAfterTyp ws (TVar i) = map TVar $ takeWhile (/= i) $ wsToVars ws
getVarsAfterTyp ws x = error (show x ++ "is not a type")

prec :: [Work] -> Typ -> Typ -> Bool
prec w varA varB = varA `elem` getVarsBeforeTyp w varB

getVarsBetweenTyp :: [Work] -> Typ -> Typ -> [Typ]
getVarsBetweenTyp ws (TVar i) (TVar j) = map TVar $ takeWhile (/= i) $ dropWhile (/= j) $ wsToVars ws
getVarsBetweenTyp ws x y = error (show x ++ "or" ++ show y ++ "is not a type")

getExWLBetweenExTyp :: [Work] -> Typ -> Typ -> [Work]
getExWLBetweenExTyp ws varA varB = map (getWorkFromExTyp ws) (getVarsBetweenTyp ws varA varB)

getWorkFromExTyp :: [Work] -> Typ -> Work
getWorkFromExTyp ((WExVar j lbs ubs):ws) (TVar (Right i))
  | i == j = WExVar j lbs ubs
  | otherwise = getWorkFromExTyp ws (TVar (Right i))
getWorkFromExTyp (w:ws) (TVar (Right i)) = getWorkFromExTyp ws (TVar (Right i))
getWorkFromExTyp [] (TVar (Right i)) = error (show (TVar (Right i)) ++ "not found in WL!")
getWorkFromExTyp _ t = error (show t ++ "is not a ExVar")

getLastExVar :: [Work] -> Typ -> Maybe Typ
getLastExVar ws typ
  | null (fv typ) = Nothing
  | otherwise = getLastExVarHelper (fv typ) Nothing <&> fst
                where getLastExVarHelper :: [Typ] -> Maybe (Typ, Int) -> Maybe (Typ, Int)
                      getLastExVarHelper (var : vars) oldRes@(Just (oldVar, oldLength))
                        | newLength < oldLength = getLastExVarHelper vars (Just (var, newLength))
                        | otherwise =  getLastExVarHelper vars oldRes
                        where newLength = length (getVarsBeforeTyp ws var)
                      getLastExVarHelper (var : vars) Nothing = getLastExVarHelper vars (Just (var, length (getVarsAfterTyp ws var)))
                      getLastExVarHelper [] res = res

gatherExVarsToMove :: [Work] -> Typ -> Typ -> [Work]
gatherExVarsToMove ws targetTyp arrowTyp =  map (getWorkFromExTyp ws)
  (gatherExVarsHelp ws targetTyp (map (getWorkFromExTyp ws) (fv arrowTyp)) [])

gatherExVarsHelp :: [Work] -> Typ -> [Work] -> [(Typ, Int)] -> [Typ]
gatherExVarsHelp subWL var (WExVar i ubs lbs : ws) res =
  gatherExVarsHelp subWL var (map (getWorkFromExTyp ws) (filter (`elem` map fst newRes) (fvInBounds lbs ubs)) ++ ws) newRes
  where
    newRes = nub ((TVar (Right i), length (getVarsBeforeTyp ws var)) : res)
gatherExVarsHelp _ var (w : ws) res = error (show w ++ "is not a ExVar")
gatherExVarsHelp _ var [] res = map fst (sortBy (\(_,a) (_,b) -> compare a b) res)

rearrangeWL :: [Work] -> Typ -> [Typ] -> [Work]
rearrangeWL ws var (varToMove : varsToMove)
  | var `elem` fvInVarBounds ws varToMove = error "Cyclic Dependency"
  | otherwise = rearrangeWL (rearrangeWLHelper ws) var varsToMove
  where rearrangeWLHelper = undefined
rearrangeWL ws var [] = ws

updateBoundWL :: Typ -> (Bound, Typ) -> [Work] -> [Work]
-- match once and no more recursion
updateBoundWL var@(TVar (Right i)) bound (WExVar j lbs ubs : ws)
  | i == j =
      case bound of
        (LB, typ) -> WExVar j (typ:lbs) ubs : ws
        (UB, typ) -> WExVar j lbs (typ:ubs) : ws
  | otherwise = WExVar j lbs ubs : updateBoundWL var bound ws
updateBoundWL var bound (w:ws) = w : updateBoundWL var bound ws
updateBoundWL var bound [] = error "Var not found!"

addTypsBefore :: Typ -> [Typ] -> [Work] -> [Work]
addTypsBefore var@(TVar (Right i)) new_vars (WExVar j lbs ubs : ws)
  | i == j = WExVar j lbs ubs : map typToWork new_vars ++ ws
  | otherwise = WExVar j lbs ubs : addTypsBefore var new_vars ws
  where
    typToWork :: Typ -> Work
    typToWork (TVar (Left i)) = WVar i
    typToWork (TVar (Right i)) = WExVar i [] []
    typToWork _ = error "Incorrect typeToWork call"
addTypsBefore var new_vars (w:ws) = w : addTypsBefore var new_vars ws
addTypsBefore var new_vars [] = error ("Typ " ++ show var ++ "is not in the worklist")

step :: Int -> [Work] -> (Int, [Work], String)
step n (WVar i : ws)                            = (n, ws, "Garbage Collection")     -- 01 
step n (WExVar i lbs ubs : ws)               =                                   -- 02
  (n, [Sub lTyp uTyp | lTyp <- lbs, uTyp <- ubs] ++ ws, "SUnfoldBounds")
step n (Sub TInt TInt : ws)                     = (n, ws, "SInt")                   -- 03
step n (Sub (TVar i) (TVar j) : ws)| i == j     = (n, ws, "SUVar")                  -- 04 + 05
step n (Sub (TArrow a b) (TArrow c d) : ws)     =                                   -- 06
  (n, Sub b d : Sub c a : ws, "SArrow")

step n (Sub a (TForall g) : ws)                 =                                   -- 08
  (n+1, Sub a (g (TVar (Left n))) : WVar n : ws, "SForallR")
step n (Sub (TForall g) b : ws)                 =                                   -- 07
  (n+1, Sub (g (TVar (Right n))) b : WExVar n [] [] : ws, "SForallL")

step n (Sub (TVar (Right i)) (TArrow a b) : ws)                                    -- 09
  | mono a && mono b = undefined
  | otherwise = (n+2, Sub (TArrow a1 a2) (TArrow a b) : updateBoundWL (TVar (Right i)) (UB, a1_a2) (addTypsBefore (TVar (Right i)) [a1, a2] ws), "SplitL")
                where
                  a1 = TVar (Right n)
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2
step n (Sub (TArrow a b) (TVar (Right i)) : ws)                                     -- 10
  | mono a && mono b = undefined
  | otherwise = (n+2,  Sub (TArrow a b) (TArrow a1 a2) : updateBoundWL (TVar (Right i)) (LB, a1_a2) (addTypsBefore (TVar (Right i)) [a1, a2] ws), "SplitR")
                where
                  a1 = TVar $ Right n
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2

step n (Sub (TVar (Right i)) (TVar (Left j)) : ws)                                  -- 11
  | prec ws (TVar (Left j)) (TVar (Right i))  = (n, updateBoundWL (TVar (Right i)) (UB, TVar (Left j)) ws, "SolveLVar")
  | otherwise = error "Incorrect var order in step call!"
step n (Sub (TVar (Left j)) (TVar (Right i))  : ws)                                 -- 12
  | prec ws (TVar (Left j)) (TVar (Right i)) = (n, updateBoundWL (TVar (Right i)) (LB, TVar (Left j)) ws, "SolveRVar")
  | otherwise = error "Incorrect var order in step call"

step n (Sub (TVar (Right i)) TInt : ws) =                                           -- 13
  (n, updateBoundWL (TVar (Right i)) (UB, TInt) ws, "SolveLInt")
step n (Sub TInt (TVar (Right i)) : ws) =                                           -- 14
  (n, updateBoundWL (TVar (Right i)) (LB, TInt) ws, "SolveRInt")
step n (Sub (TVar (Right i)) (TVar (Right j)) : ws)                                 -- 15 & 16
  | prec ws (TVar (Right i)) (TVar (Right j)) = (n, updateBoundWL (TVar (Right j)) (LB, TVar (Right i)) ws, "SolveLExtVar")
  | prec ws (TVar (Right j)) (TVar (Right i)) = (n, updateBoundWL (TVar (Right i)) (UB, TVar (Right j)) ws, "SolveRExtVar")

step n _  = error "Incorrect step call!"


check :: Int -> [Work] -> String
check n [] = "Success!"
check n ws =
  let (m,ws',s1) = step n ws
      s2         = check m ws'
  in ("   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ " }\n" ++ s2)


t1 = TForall (\a -> TArrow a a)


t2 = TArrow t1 (TForall (\a -> TArrow a a))


t3 = TArrow TInt TInt


chk = putStrLn .  check 0

t5 = TForall (\t -> t)

t6 = TArrow TInt TInt
t7 = TArrow t6 t6

test1 = chk [Sub t3 t3]
test2 = chk [Sub t1 t3]
test3 = chk [Sub t5 t3]
test4 = chk [Sub t5 t1]
test5 = chk [Sub t1 t6]
test6 = chk [Sub t6 t3]

test7 = chk [Sub t5 t7]

test8 = chk [Sub (TForall $ \a -> TArrow a a) (TArrow t5 (TArrow TInt TInt))]

tEx = TVar . Right

test9 = putStrLn  $
  check 4 [Sub ex1 (TArrow TInt ex2), Sub ex2 (TArrow TInt ex1), WExVar 2 [] [], WExVar 1 [] []]

ex1 = tEx 1
ex2 = tEx 2
ex3 = tEx 3
ws1 = [Sub ex1 (TArrow TInt (TArrow ex2 ex3)), Sub ex2 (TArrow TInt ex1),  WExVar 2 [] [],  WExVar 3 [] [], WExVar 1 [] []]

testGetLastVar :: Maybe Typ
testGetLastVar = getLastExVar ws1 (TArrow TInt (TArrow ex2 ex3))

testGetVarsBetweenTyp :: Maybe [Typ]
testGetVarsBetweenTyp = getLastExVar ws1 (TArrow TInt (TArrow ex2 ex3)) <&> getVarsBetweenTyp ws1 ex1

testGetExWLBetweenExTyp :: [Work]
testGetExWLBetweenExTyp = getExWLBetweenExTyp ws1 ex1 ex2

testGatherExVarsToMove = gatherExVarsToMove ws1 ex1 (TArrow TInt (TArrow ex2 ex3))