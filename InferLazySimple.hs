{-# LANGUAGE LambdaCase #-}
module InferLazySimple where

import Control.Exception
import Prelude hiding (flip)
import Data.List
import Data.Functor

import Debug.Trace
import GHC.Exts (Constraint)

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
    add constraint to ^a and move when monotype (A -> B)
      
10. T[lbs <: ^a < ubs] |- A -> B <: ^a --> T[^a1,^a2, lbs U {^a1,^a2} <: ^a < ubs] |- A -> B <: ^a1 -> ^a2   
          when not monotype (A->B)  
    add constraint to ^a and move when monotype (A -> B)

11. T[a][lbs <: ^b < ubs] |- a <: ^b   --> T[a][lbs U {a} <: ^b < ub] 
12. T[a][lbs <: ^b < ubs] |- ^b <: a   --> T[a][lbs <: ^b < ub U {a}] 
13. T[lbs <: ^b < ubs] |- Int <: ^b    --> T[a][lbs U {Int} <: ^b < ub] 
14. T[lbs <: ^b < ubs] |- ^b <: Int    --> T[a][lb s<: ^b < ub U {Int}] 

15. T[^a][lbs <: ^b < ubs] |- ^a <: ^b --> T[^a][lb U {^a} <: ^b < ub] 
16. T[^a][lbs <: ^b < ubs] |- ^b <: ^a --> T[^a][lb <: ^b < ub U {^a}] 

-}

data Typ = TVar (Either Int Int) | TInt | TForall (Typ -> Typ) | TArrow Typ Typ

-- Consider changing to set
data Work = WVar Int | WExVar Int [Typ] [Typ] | Sub Typ Typ deriving Eq

data BoundTyp = LB | UB

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

worksToTyps :: [Work] -> [Either Int Int]
worksToTyps = concatMap (\case
                        WVar i -> [Left i]
                        WExVar i _ _ -> [Right i]
                        _ -> []
                     )

fvInBounds :: [Typ] -> [Typ] -> [Typ]
fvInBounds lbs ubs = concatMap fv lbs `union` concatMap fv ubs

fvInVarBounds :: [Work] -> Typ -> [Typ]
fvInVarBounds wl var = case getWorkFromExTyp wl var of
                         (WExVar _ lbs ubs) -> fvInBounds lbs ubs
                         _ -> error "Bug: Impossible in fvInVarBounds"

getVarsBeforeTyp :: [Work] -> Typ -> [Typ]
getVarsBeforeTyp wl (TVar i) = map TVar $ dropWhile (/= i) $ worksToTyps wl
getVarsBeforeTyp wl x = error (show x ++ "is not a type")

getVarsAfterTyp :: [Work] -> Typ -> [Typ]
getVarsAfterTyp wl (TVar i) = map TVar $ takeWhile (/= i) $ worksToTyps wl
getVarsAfterTyp wl x = error (show x ++ "is not a type")

prec :: [Work] -> Typ -> Typ -> Bool
prec w varA varB = varA `elem` getVarsBeforeTyp w varB

getVarsBetweenTyp :: [Work] -> Typ -> Typ -> [Typ]
getVarsBetweenTyp wl (TVar i) (TVar j) = map TVar $ takeWhile (/= i) $ dropWhile (/= j) $ worksToTyps wl
getVarsBetweenTyp wl x y = error (show x ++ "or" ++ show y ++ "is not a type")

getExWLBetweenExTyp :: [Work] -> Typ -> Typ -> [Work]
getExWLBetweenExTyp wl varA varB = map (getWorkFromExTyp wl) (getVarsBetweenTyp wl varA varB)

getExWLAfterExTyp :: [Work] -> Typ -> [Work]
getExWLAfterExTyp wl varA = map (getWorkFromExTyp wl) (getVarsAfterTyp wl varA)

getWorkFromExTyp :: [Work] -> Typ -> Work
getWorkFromExTyp ((WExVar j lbs ubs):wl) (TVar (Right i))
  | i == j = WExVar j lbs ubs
  | otherwise = getWorkFromExTyp wl (TVar (Right i))
getWorkFromExTyp (w:wl) (TVar (Right i)) = getWorkFromExTyp wl (TVar (Right i))
getWorkFromExTyp [] (TVar (Right i)) = error (show (TVar (Right i)) ++ "not found in WL!")
getWorkFromExTyp _ t = error (show t ++ "is not a ExVar")

gatherExVarsToMove :: [Work] -> Typ -> Typ -> [Work]
gatherExVarsToMove wl targetTyp arrowTyp =  map (getWorkFromExTyp wl)
  -- only ExVars after the target ExVar need moving forward
  (gatherExVarsHelp (getExWLAfterExTyp wl targetTyp) (map (getWorkFromExTyp wl) (fv arrowTyp)) [])

-- args : WL, works to process, result accumulator
gatherExVarsHelp :: [Work] -> [Work] -> [(Typ, Int)] -> [Typ]
gatherExVarsHelp wl (WExVar i ubs lbs : ws) res =
  gatherExVarsHelp wl (map (getWorkFromExTyp ws) (filter (`elem` map fst newRes) (fvInBounds lbs ubs)) ++ ws) newRes
  where
    newRes
      -- only ExVars after the target ExVar need moving forward
     | not (null (getVarsBeforeTyp wl (TVar (Right i)))) = nub ((TVar (Right i), length (getVarsBeforeTyp wl (TVar (Right i)))) : res)
     | otherwise = res
gatherExVarsHelp _ [] res = map fst (sortBy (\(_,a) (_,b) -> compare a b) res)
gatherExVarsHelp _ (w : ws) res = error "Bug: Impossible in gatherExVarsHelp!"

-- args : WL, target ExVar, ExVars to move
rearrangeWL :: [Work] -> Typ -> [Work] -> Either String [Work]
rearrangeWL wl targetVar@(TVar (Right i)) (WExVar j lbsj ubsj : varsToMove)
  | targetVar `elem` (concatMap fv lbsj `union` concatMap fv ubsj) =
      Left ("Error: Cyclic Dependency of " ++ show (TVar (Right i)) ++ " and " ++ show (TVar (Right j)) ++ "!")
  | otherwise = rearrangeWL (rearrangeWLHelper wl) targetVar varsToMove
  where
    rearrangeWLHelper (WExVar k lbsk ubsk : wl)
      | k == j = rearrangeWLHelper wl
      | k == i = WExVar k lbsk ubsk : WExVar j lbsj ubsj : wl
      | otherwise = WExVar k lbsk ubsk : rearrangeWLHelper wl
    rearrangeWLHelper (w : wl) = w : rearrangeWLHelper wl
    rearrangeWLHelper [] = error "Bug: target type not in WL!"
rearrangeWL wl targetVar (var:varWL) = error ("Bug: " ++ show var ++ "should not be rearranged!")
rearrangeWL wl targetVar [] = Right wl

updateBoundWL :: Typ -> (BoundTyp, Typ) -> [Work] -> [Work]
-- match once and no more recursion
updateBoundWL var@(TVar (Right i)) bound (WExVar j lbs ubs : ws)
  | i == j =
      case bound of
        (LB, typ) -> WExVar j (typ:lbs) ubs : ws
        (UB, typ) -> WExVar j lbs (typ:ubs) : ws
  | otherwise = WExVar j lbs ubs : updateBoundWL var bound ws
updateBoundWL var bound (w:ws) = w : updateBoundWL var bound ws
updateBoundWL var bound [] = error "Bug: Var not found!"

addTypsBefore :: Typ -> [Typ] -> [Work] -> [Work]
addTypsBefore var@(TVar (Right i)) new_vars (WExVar j lbs ubs : ws)
  | i == j = WExVar j lbs ubs : map typToWork new_vars ++ ws
  | otherwise = WExVar j lbs ubs : addTypsBefore var new_vars ws
  where
    typToWork :: Typ -> Work
    typToWork (TVar (Left i)) = WVar i
    typToWork (TVar (Right i)) = WExVar i [] []
    typToWork _ = error "Bug: Incorrect typeToWork call"
addTypsBefore var new_vars (w:ws) = w : addTypsBefore var new_vars ws
addTypsBefore var new_vars [] = error ("Bug: Typ " ++ show var ++ "is not in the worklist")

step :: Int -> [Work] -> (Int, Either String [Work], String)
step n (WVar i : ws)                            = (n, Right ws, "Garbage Collection")     -- 01 
step n (WExVar i lbs ubs : ws)                  =                                      -- 02
  (n, Right $ [Sub lTyp uTyp | lTyp <- lbs, uTyp <- ubs] ++ ws, "SUnfoldBounds")
step n (Sub TInt TInt : ws)                     = (n, Right ws, "SInt")                   -- 03
step n (Sub (TVar i) (TVar j) : ws)| i == j     = (n, Right ws, "SUVar")                  -- 04 + 05
step n (Sub (TArrow a b) (TArrow c d) : ws)     =                                   -- 06
  (n, Right $  Sub b d : Sub c a : ws, "SArrow")

step n (Sub a (TForall g) : ws)                 =                                   -- 08
  (n+1, Right $ Sub a (g (TVar (Left n))) : WVar n : ws, "SForallR")
step n (Sub (TForall g) b : ws)                 =                                   -- 07
  (n+1, Right $  Sub (g (TVar (Right n))) b : WExVar n [] [] : ws, "SForallL")

step n (Sub (TVar (Right i)) (TArrow a b) : ws)                                     -- 09
  | mono (TArrow a b) =
    case rearrangeWL ws (TVar (Right i)) (gatherExVarsToMove ws (TVar (Right i)) (TArrow a b)) of
      Left e -> (0, Left e, "SplitL mono")
      Right wl -> (n, Right $  updateBoundWL (TVar (Right i)) (UB, TArrow a b) wl, "SplitL mono")
  | otherwise = (n+2, Right $ Sub (TArrow a1 a2) (TArrow a b) : updateBoundWL (TVar (Right i)) (UB, a1_a2)
      (addTypsBefore (TVar (Right i)) [a1, a2] ws), "SplitL")
                where
                  a1 = TVar (Right n)
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2

step n (Sub (TArrow a b) (TVar (Right i)) : ws)                                     -- 10
  | mono (TArrow a b) =
    case rearrangeWL ws (TVar (Right i)) (gatherExVarsToMove ws (TVar (Right i)) (TArrow a b)) of
      Left e -> (0, Left e, "SplitL mono")
      Right wl -> (n, Right $ updateBoundWL (TVar (Right i)) (LB, TArrow a b) wl, "SplitR mono")
  | otherwise = (n+2,  Right $ Sub (TArrow a b) (TArrow a1 a2) : updateBoundWL (TVar (Right i)) (LB, a1_a2)
      (addTypsBefore (TVar (Right i)) [a1, a2] ws), "SplitR")
                where
                  a1 = TVar $ Right n
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2

step n (Sub (TVar (Right i)) (TVar (Left j)) : ws)                                  -- 11
  | prec ws (TVar (Left j)) (TVar (Right i))  = (n, Right $ updateBoundWL (TVar (Right i)) (UB, TVar (Left j)) ws, "SolveLVar")
  | otherwise = error "Bug: Incorrect var order in step call!"
step n (Sub (TVar (Left j)) (TVar (Right i))  : ws)                                 -- 12
  | prec ws (TVar (Left j)) (TVar (Right i)) = (n, Right $ updateBoundWL (TVar (Right i)) (LB, TVar (Left j)) ws, "SolveRVar")
  | otherwise = error "Bug: Incorrect var order in step call"

step n (Sub (TVar (Right i)) TInt : ws) =                                           -- 13
  (n, Right $ updateBoundWL (TVar (Right i)) (UB, TInt) ws, "SolveLInt")
step n (Sub TInt (TVar (Right i)) : ws) =                                           -- 14
  (n, Right $ updateBoundWL (TVar (Right i)) (LB, TInt) ws, "SolveRInt")
step n (Sub (TVar (Right i)) (TVar (Right j)) : ws)                                 -- 15 & 16
  | prec ws (TVar (Right i)) (TVar (Right j)) = (n, Right $ updateBoundWL (TVar (Right j)) (LB, TVar (Right i)) ws, "SolveLExtVar")
  | prec ws (TVar (Right j)) (TVar (Right i)) = (n, Right $ updateBoundWL (TVar (Right i)) (UB, TVar (Right j)) ws, "SolveRExtVar")

step n _  = (n, Left "No matched pattern", "None")


checkAndShow :: Int -> [Work] -> String
checkAndShow n [] = "Success!"
checkAndShow n ws =
  case ws' of
    Left e -> "Failure!"
    Right wl -> s2
      where s2 = "   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ " }\n" ++ checkAndShow m wl
  where
    (m, ws', s1) = step n ws


check :: Int -> [Work] -> String
check n [] = "Success!"
check n ws =
  let (m,ws',s1) = step n ws
  in
    case ws' of
      Left e -> "Failure!"
      Right wl -> check m wl


t1 = TForall (\a -> TArrow a a)


t2 = TArrow t1 (TForall (\a -> TArrow a a))


t3 = TArrow TInt TInt

chkAndShow = putStrLn .  checkAndShow 0

chk = check 0

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
ws1 = [Sub ex1 (TArrow TInt (TArrow ex2 ex3)), Sub ex2 (TArrow TInt ex1),  WExVar 2 [] [],  WExVar 1 [] [], WExVar 3 [] []]

testGetExWLBetweenExTyp :: [Work]
testGetExWLBetweenExTyp = getExWLBetweenExTyp ws1 ex1 ex2

testGatherExVarsToMove :: [Work]
testGatherExVarsToMove = gatherExVarsToMove ws1 ex1 (TArrow TInt (TArrow ex2 ex3))

testRearrangeWL :: Either String [Work]
testRearrangeWL = rearrangeWL ws1 (tEx 1) testGatherExVarsToMove