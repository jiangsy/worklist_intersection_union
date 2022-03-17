{-# LANGUAGE LambdaCase, MultiWayIf #-}
module InferLazy where

import Data.List

import LazyDef
import TestCase
{- A lazy subtyping algorithm:

A,B := a | ^a | Int | A -> B | forall a. A | 
T ::= . | T,a | T, lbs <: ^a <: ubs |- A <: B

Algorithm:

[#splits, #forall, #existential, |wl|]

(3 * #splits + #forall + #existential, |wl|)

01. T, a                               --> T                                                      (rule 1)
[0, 0, 0, -1] -> (0, -1)

02. T[^a] |- [l1..ln] <: ^a <:[u1..um] --> T |- l1 <: u1 .... |- ln <: lm (n x m)                 (rule 2)
[0, 0, -1, +(n*m-1)] -> (-1, +?)

03. T |- Int <: Int                    --> T                                                      (rule 5)
[0, 0, 0, -1] -> (0, -1)

04. T[a]  |- a <: a                    --> T                                                      (rule 6)
[0, 0, 0, -1] -> (0, -1)

05. T[^a] |- ^a <: ^a                  --> T                                                      (rule 7)
[0, 0, 0, -1] -> (0, -1)

06. T |- A -> B <: C -> D              --> T |- C <: A |- B <: D                                  (rule 8)
[0, 0, 0, -2] -> (0, -2)

07. T |- forall a . B <: C             --> T,^a |- [^a/a] B <: C                                  (rule 9)
[0, -1, +1, -1] -> (0, -1)

08. T |- A <: forall b . B             --> T,b |- A <: C                                          (rule 10)
[0, -1, 0, -1] -> (-1, -1)

09. T[lbs <: ^a < ubs] |- ^a <: A -> B --> T[^a1,^a2,lbs <: ^a < ubs ∪ {^a1->^a2}] |- ^a1 -> ^a2 <: A -> B  
          when not monotype (A->B)  
[-1, 0, +2, +?] -> (-1, +?)

09'. T[lbs <: ^a < ubs] |- ^a <: A -> B --> ([A->B/^a]_[] T) [lbs <: ^a < ubs ∪ {A->B}] |-
          when monotype (A->B)  
[0, 0, 0, -1] -> (0, -1)

10. T[lbs <: ^a < ubs] |- A -> B <: ^a --> T[^a1,^a2, lbs ∪ {^a1,^a2} <: ^a < ubs] |- A -> B <: ^a1 -> ^a2   
          when not monotype (A->B)  
[-1, 0, +2, +?] -> (-1, +?)

10'. T[lbs <: ^a < ubs] |- A -> B <: ^a --> ([A->B/^a]_[] T) [lbs ∪ {A->B} <: ^a < ubs] |- 
          when monotype (A->B)  
[0, 0, 0, -1] -> (0, -1)

11. T[a][lbs <: ^b < ubs] |- a <: ^b   --> T[a][lbs ∪ {a} <: ^b < ubs] 
[0, 0, 0, -1] -> (0, -1)

12. T[a][lbs <: ^b < ubs] |- ^b <: a   --> T[a][lbs <: ^b <: ubs ∪ {a}] 
[0, 0, 0, -1] -> (0, -1)

13. T[lbs <: ^b < ubs] |- Int <: ^b    --> T[a][lbs U {Int} <: ^b <: ubs] 
[0, 0, 0, -1] -> (0, -1)

14. T[lbs <: ^b < ubs] |- ^b <: Int    --> T[a][lbs <: ^b <: ubs ∪ {Int}] 
[0, 0, 0, -1] -> (0, -1)

15. T[^a][lbs <: ^b < ubs] |- ^a <: ^b --> T[^a][lbs ∪ {^a} <: ^b < ubs] 
[0, 0, 0, -1] -> (0, -1)

16. T[^a][lbs <: ^b < ubs] |- ^b <: ^a --> T[^a][lbs <: ^b < ubs ∪ {^a}] 
[0, 0, 0, -1] -> (0, -1)

--------------
[A/^a]_E T
--------------

[A/^a]_E (T,L <: ^a <: R)   = T, reverse E, L <: ^a <: R                 ^a notin fv(A) and ^a notin fv(E)
[A/^a]_E (T,L <: ^b <: R)   = [A/^a]_E T, L <: ^b <: R          ^b notin FV(A + E)
[A/^a]_E (T, L <: ^b <: R)  = [A/^a]_{E, L <: ^b <: R} T        (^b in FV(A) or ^b in FV(E)) and ^a notin(L+R)
[A/^a]_E (T, a)             = [A/^a]_{E} T, a                   a notin FV(A+ E) 
[A/^a]_E (T |- B <: C)      = [A/^a]_(E, B <: C) T             fv(B + C) ∩ fv(A + E) != Φ
[A/^a]_E (T |- B <: C)      = [A/^a]_(E) (T |- B <: C)         fv(B + C) ∩ fv(A + E) = Φ

-}


mono :: Typ -> Bool
mono (TForall g)  = False
mono (TArrow a b) = mono a && mono b
mono _            = True

fv :: Typ -> [Typ]
fv (TVar i)         = [TVar i]
fv (TArrow t1 t2)   = fv t1 `union` fv t2
fv (TForall g)      = fv (g TInt)
fv _                = []

fvInWork :: Work -> [Typ]
fvInWork (WVar i) = []
fvInWork (WExVar j lbs ubs) = nub (concatMap fv lbs) `union` nub (concatMap fv ubs)
fvInWork (Sub t1 t2) = nub (fv t1) `union` nub (fv t2)

worksToTyps :: [Work] -> [Either Int Int]
worksToTyps = concatMap (\case
                          WVar i -> [Left i]
                          WExVar i _ _ -> [Right i]
                          _ -> []
                        )

getVarsBeforeTyp :: [Work] -> Typ -> [Typ]
getVarsBeforeTyp wl (TVar i) = map TVar $ dropWhile (/= i) $ worksToTyps wl
getVarsBeforeTyp wl x = error ("Bug:" ++ show x ++ "is not a type")

getVarsAfterTyp :: [Work] -> Typ -> [Typ]
getVarsAfterTyp wl (TVar i) = map TVar $ takeWhile (/= i) $ worksToTyps wl
getVarsAfterTyp wl x = error ("Bug:" ++ show x ++ "is not a type")

prec :: [Work] -> Typ -> Typ -> Bool
prec w varA varB = varA `elem` getVarsBeforeTyp w varB

updateBoundInWL :: Typ -> (BoundTyp, Typ) -> [Work] -> Either String [Work]
-- match once and no more recursion
updateBoundInWL var@(TVar (Right i)) bound (WExVar j lbs ubs : ws)
  | i == j =
      case bound of
        (LB, typ) -> if var `elem` fVars then Left $  "Error: Cyclic Dependency of " ++ show var ++ " self!"  else Right $ WExVar j (typ:lbs) ubs : ws
          where fVars = nub $ fv typ
        (UB, typ) -> if var `elem` fVars then Left $  "Error: Cyclic Dependency of " ++ show var ++ " self!" else Right $ WExVar j lbs (typ:ubs) : ws
          where fVars = nub $ fv typ
  | otherwise = updateBoundInWL var bound ws >>= (\ws' -> Right $ WExVar j lbs ubs : ws')
updateBoundInWL var bound (w:ws) = updateBoundInWL var bound ws >>= (\ws' -> Right $ w : ws')
updateBoundInWL var bound [] = error "Bug: Var not found!"

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

-- https://stackoverflow.com/questions/27726739/implementing-an-efficient-sliding-window-algorithm-in-haskell
windows :: Int -> [Typ] -> [[Typ]]
windows n = foldr (zipWith (:)) (repeat []) . take n . tails

generateOneSideConstraints :: [Typ] -> [Work]
generateOneSideConstraints bounds = map (\ts -> Sub (head ts) (last ts)) (windows 2 bounds)

-- targetTyp, boundTyp, worklist
carryBackInWL :: Typ -> Typ -> [Work] -> Either String [Work]
carryBackInWL targetTyp@(TVar (Right i)) boundTyp wl =
    carryBackInWLHelper wl [] fVars
    where
      carryBackInWLHelper :: [Work] -> [Work] -> [Typ] -> Either String [Work]
      carryBackInWLHelper (wexvar@(WExVar j lbs ubs):wl') toCarryBack fvs
        | i == j = Right $ wexvar:(reverse toCarryBack++wl')
        | otherwise = if
          | (TVar (Right j) `notElem` fvs) ->
            carryBackInWLHelper wl' toCarryBack fvs >>= (\wl'' -> Right $ wexvar:wl'')
          | (TVar (Right j) `elem` fvs) && (TVar (Right i) `notElem` fvInWork wexvar) ->
            carryBackInWLHelper wl' (wexvar:toCarryBack) (fvInWork wexvar `union` fvs)
          | otherwise -> Left $ "Error: Cyclic Dependency of " ++ show targetTyp ++ " and " ++ show (TVar (Right j))
      carryBackInWLHelper (wvar@(WVar j):wl') toCarryBack fvs
        | TVar (Left j) `elem` fvs = Left $ "Error: Cyclic Dependency of " ++ show targetTyp ++ " and " ++ show (TVar (Left j))
        | otherwise = carryBackInWLHelper wl' toCarryBack fvs >>= (\wl'' -> Right $ wvar:wl'')
      carryBackInWLHelper (wsub@(Sub t1 t2):wl') toCarryBack fvs =
        carryBackInWLHelper wl' toCarryBack fvs >>= (\wl'' -> Right $ wsub:wl'')
      carryBackInWLHelper [] _ _ = Left "Bug: Impossible in carryBackInWL"
      fVars :: [Typ]
      fVars = nub $ fv boundTyp
carryBackInWL _ _ _ = error "Bug: Wrong targetTyp in carryBackInWL"


step :: Int -> [Work] -> (Int, Either String [Work], String)
step n (WVar i : ws)                            = (n, Right ws, "Garbage Collection")     -- 01 
step n (WExVar i lbs ubs : ws)  
  | null lbs && null ubs = (n, Right ws, "SUnfoldBoundsEmptyLU")
  | null lbs = (n, Right $ [Sub (head ubs) uTyp | uTyp <- tail ubs] ++ ws, "SUnfoldBoundsEmptyL")                
  | null ubs = (n, Right $ [Sub (head lbs) uTyp | uTyp <- tail lbs] ++ ws, "SUnfoldBoundsEmptyU")                 
  | otherwise = (n, Right $ [Sub lTyp uTyp | lTyp <- lbs, uTyp <- ubs] ++ ws, "SUnfoldBounds")
step n (Sub TInt TInt : ws)                     = (n, Right ws, "SInt")                   -- 03
step n (Sub TBool TBool : ws)                   = (n, Right ws, "SBool")                  -- 03

step n (Sub (TVar i) (TVar j) : ws)| i == j     = (n, Right ws, "SUVar")                  -- 04 + 05
step n (Sub (TArrow a b) (TArrow c d) : ws)     =                                         -- 06
  (n, Right $  Sub b d : Sub c a : ws, "SArrow")

step n (Sub a (TForall g) : ws)                 =                                         -- 08
  (n+1, Right $ Sub a (g (TVar (Left n))) : WVar n : ws, "SForallR")
step n (Sub (TForall g) b : ws)                 =                                         -- 07
  (n+1, Right $  Sub (g (TVar (Right n))) b : WExVar n [] [] : ws, "SForallL")

step n (Sub (TVar (Right i)) (TArrow a b) : ws)                                           -- 09
   | not $ mono (TArrow a b)                    =
    (n+2, updateBoundInWL (TVar (Right i)) (UB, a1_a2) (addTypsBefore (TVar (Right i)) [a1, a2] ws) >>=
      (\wl' -> Right $ Sub (TArrow a1 a2) (TArrow a b):wl'), "SplitL")
                where
                  a1 = TVar (Right n)
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2

step n (Sub (TArrow a b) (TVar (Right i)) : ws)                                           -- 10
  | not $ mono (TArrow a b)                     =
    (n+2, updateBoundInWL (TVar (Right i)) (LB, a1_a2) (addTypsBefore (TVar (Right i)) [a1, a2] ws) >>= 
      (\wl' -> Right $ Sub (TArrow a b) (TArrow a1 a2) : wl')  , "SplitR")
                where
                  a1 = TVar $ Right n
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2

step n (Sub (TVar (Right i)) (TVar (Right j)) : ws)                                       -- 15 & 16
  | prec ws (TVar (Right i)) (TVar (Right j))   =
    (n, updateBoundInWL (TVar (Right j)) (LB, TVar (Right i)) ws, "SolveLExtVar")
  | prec ws (TVar (Right j)) (TVar (Right i))   =
    (n, updateBoundInWL (TVar (Right i)) (UB, TVar (Right j)) ws, "SolveRExtVar")

step n (Sub (TVar (Right i)) t : ws)                                        -- 11
  | mono t                                      =
    (n, carryBackInWL (TVar (Right i)) t ws >>= 
      updateBoundInWL (TVar (Right i)) (UB, t), "Solve mono R")
  | otherwise =  error $ "Bug: Incorrect " ++ show t ++ " !"
step n (Sub t (TVar (Right i))  : ws)                                       -- 12
  | mono t                                      =
    (n, carryBackInWL (TVar (Right i)) t ws >>= 
      updateBoundInWL (TVar (Right i)) (LB, t), "Solve mono L")
  | otherwise = error $ "Bug: Incorrect " ++ show t ++ " !"

step n _                                        = (n, Left "No matched pattern", "None")


checkAndShow :: Int -> [Work] -> String
checkAndShow n [] = "Success!"
checkAndShow n ws =
  case ws' of
    Left e -> "   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ replicate (20 - length s1) ' ' ++ "Size: " ++ show (size ws) ++ " }\n" ++ e
    Right wl -> s2
      where s2 = "   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ replicate (20 - length s1) ' ' ++ "Size: " ++ show (size ws) ++ " }\n" ++ checkAndShow m wl
  where
    (m, ws', s1) = step n ws


check :: Int -> [Work] -> String
check n [] = "Success!"
check n wl =
  let (n', res, s1) = step n wl
  in
    case res of
      Left e -> "Failure!"
      Right wl' -> check n' wl'


size :: [Work] -> (Int,Int)
size ws = (measure1 ws, sizeWL ws)

-- Measure 1

measure1 :: [Work] -> Int
measure1 ws = 3 * splits ws + foralls ws + existentials ws

splits :: [Work] -> Int
splits []              = 0
splits (WVar {} : ws)   = splits ws
splits (WExVar {}:ws) = splits ws
splits (Sub a b : ws)  = splitsSub a b + splits ws

splitsSub :: Typ -> Typ -> Int
splitsSub (TVar (Right i)) t1@(TArrow _ _) = splitsTyp t1
splitsSub t1@(TArrow _ _) (TVar (Right i)) = splitsTyp t1
splitsSub (TArrow a b) (TArrow c d) =
  splitsSub c a + splitsSub b d
splitsSub a (TForall g) = splitsSub a (g (TVar (Left 0)))
splitsSub (TForall g) a = splitsSub (g (TVar (Right 0))) a
splitsSub a b           = 0

splitsTyp :: Num a => Typ -> a
splitsTyp (TArrow a b)
  | not (mono a) && not (mono b) = 1 + splitsTyp a + splitsTyp b
  | not (mono a)                 = 1 + splitsTyp a
  | not (mono b)                 = 1 + splitsTyp b
  | otherwise                    = 0
splitsTyp (TForall g)            = splitsTyp (g TInt)
splitsTyp _                      = 0

existentials :: Num a => [Work] -> a
existentials []                 = 0
existentials (WExVar {} : ws)   = 1 + existentials ws
existentials (_ : ws)           = existentials ws

foralls :: Num a => [Work] -> a
foralls []                      = 0
foralls (Sub a b : ws)          = forallsTyp a + forallsTyp b + foralls ws
foralls (_ : ws)                = foralls ws

forallsTyp :: Num a => Typ -> a
forallsTyp (TForall g)  = 1 + forallsTyp (g TInt)
forallsTyp (TArrow a b) = forallsTyp a + forallsTyp b
forallsTyp _            = 0

{-

[Int -> forall a. ^b <: ^c, ^c <: Int -> Int]

-}

-- Measure 2

sizeWL :: [Work] -> Int
sizeWL []              = 0
sizeWL (Sub a b : ws)  = sizeSub a b + sizeWL ws
sizeWL (_ : ws)        = 1 + sizeWL ws


sizeSub (TArrow a b) (TArrow c d) = 1 + sizeSub c a + sizeSub b d
sizeSub (TForall g) a             = 2 + sizeSub (g TInt) a
sizeSub a (TForall g)             = 2 + sizeSub a (g TInt)
sizeSub _ _                       = 1



chkAndShow = putStrLn .  checkAndShow 0

chk :: [Work] -> String
chk = check 0

test1 = chkAndShow [Sub t3 t3]
test2 = chkAndShow [Sub t1 t3]
test3 = chkAndShow [Sub t5 t3]
test4 = chkAndShow [Sub t5 t1]
test5 = chkAndShow [Sub t1 t6]
test6 = chkAndShow [Sub t6 t3]
test7 = chkAndShow [Sub t5 t7]
test8 = chkAndShow [Sub (TForall $ \a -> TArrow a a) (TArrow t5 (TArrow TInt TInt))]
test9 = chkAndShow [Sub ex1 (TArrow TInt ex2), Sub ex2 (TArrow TInt ex1), WExVar 2 [] [], WExVar 1 [] []]
test10 = chkAndShow [Sub (TForall (\t -> (TArrow t (TForall (\t1 -> TArrow t1 t))))) (TForall (\t -> (TArrow t (TArrow t t)))) ]
ws1 = [Sub ex1 (TArrow TInt (TArrow ex2 ex3)), Sub ex2 (TArrow TInt ex1),  WExVar 2 [] [],   WExVar 3 [] [], WExVar 1 [] []]

test12 = chkAndShow [Sub t8 t9]

ex0 = TVar (Right 0)

jimmy = putStrLn $ checkAndShow 3 [
  Sub TInt TInt,
  Sub ex0 (TArrow TInt TInt),
  Sub (TArrow ex0 (TArrow ex0 $ TForall $ \a -> a)) ex1,
  WExVar 0 [] [],
  WExVar 1 [] [],
  WExVar 2 [] []
  ]