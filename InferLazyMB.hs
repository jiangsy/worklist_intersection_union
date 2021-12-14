{-# LANGUAGE LambdaCase, MultiWayIf #-}
module InferLazyMB where

import Control.Exception
import Prelude hiding (flip)
import Data.List
import Data.Functor

import Debug.Trace
import GHC.Exts (Constraint)

import LazyDef
import TestCase
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


--------------
[A/^a]_E T
--------------

[A/^a]_E (T,L <: ^a <: R)   = T,E,L <: ^a <: R                 ^a notin fv(A) and ^a notin fv(E)
[A/^a]_E (T,L <: ^b <: R)   = [A/^a]_E T,L <: ^b <: R          ^b notin FV(A + E)
[A/^a]_E (T, L <: ^b <: R)  = [A/^a]_{E,L <: ^b <: R} T        ^b in FV(A) or ^b in FV(E) and ^a notin(L+R)
[A/^a]_E (T, a)             = [A/^a]_{E,L <: ^b <: R} T        a notin FV(A+ E) 
[A/^a]_E (T |- B <: C)      = [A/^a]_(E, B <: C) T             fv(B + C) in fv(A + E)
[A/^a]_E (T |- B <: C)      = [A/^a]_(E) (T |- B <: C)         not (fv(B + C) in fv(A + E))

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
getVarsBeforeTyp wl x = error (show x ++ "is not a type")

getVarsAfterTyp :: [Work] -> Typ -> [Typ]
getVarsAfterTyp wl (TVar i) = map TVar $ takeWhile (/= i) $ worksToTyps wl
getVarsAfterTyp wl x = error (show x ++ "is not a type")

prec :: [Work] -> Typ -> Typ -> Bool
prec w varA varB = varA `elem` getVarsBeforeTyp w varB

updateBoundInWL :: Typ -> (BoundTyp, Typ) -> [Work] -> [Work]
-- match once and no more recursion
updateBoundInWL var@(TVar (Right i)) bound (WExVar j lbs ubs : ws)
  | i == j =
      case bound of
        (LB, typ) -> WExVar j (typ:lbs) ubs : ws
        (UB, typ) -> WExVar j lbs (typ:ubs) : ws
  | otherwise = WExVar j lbs ubs : updateBoundInWL var bound ws
updateBoundInWL var bound (w:ws) = w : updateBoundInWL var bound ws
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


-- targetTyp, boundType, worklist
carryBackInWL :: Typ -> Typ -> [Work] -> Either String [Work]
carryBackInWL targetTyp@(TVar (Right i)) boundTyp wl =
  if targetTyp `elem` fVars then Left "Error: Cyclic Dependency of self" else 
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
      carryBackInWLHelper [] _ _ = Left "Error: Impossible in carryBackInWL"
      fVars :: [Typ]
      fVars = nub $ fv boundTyp 
carryBackInWL _ _ _ = error "Bug: Wrong targetTyp in carryBackInWL"


step :: Int -> [Work] -> (Int, Either String [Work], String)
step n (WVar i : ws)                            = (n, Right ws, "Garbage Collection")     -- 01 
step n (WExVar i lbs ubs : ws)                  =                                         -- 02
  (n, Right $ [Sub lTyp uTyp | lTyp <- lbs, uTyp <- ubs] ++ ws, "SUnfoldBounds")
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
  | mono (TArrow a b)                           =
    case carryBackInWL (TVar (Right i)) (TArrow a b) ws of
       Left e -> (n, Left e, "SplitL mono")
       Right wl -> (n, Right $ updateBoundInWL (TVar (Right i)) (UB, TArrow a b) wl, "SplitL mono")
  | otherwise                                   =
    (n+2, Right $ Sub (TArrow a1 a2) (TArrow a b) : updateBoundInWL (TVar (Right i)) (UB, a1_a2)
      (addTypsBefore (TVar (Right i)) [a1, a2] ws), "SplitL")
                where
                  a1 = TVar (Right n)
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2

step n (Sub (TArrow a b) (TVar (Right i)) : ws)                                           -- 10
  | mono (TArrow a b)                           =
    case carryBackInWL (TVar (Right i)) (TArrow a b) ws of
       Left e -> (n, Left e, "SplitR mono")
       Right wl -> (n, Right $ updateBoundInWL (TVar (Right i)) (LB, TArrow a b) wl, "SplitR mono")
  | otherwise                                   =
    (n+2,  Right $ Sub (TArrow a b) (TArrow a1 a2) : updateBoundInWL (TVar (Right i)) (LB, a1_a2)
      (addTypsBefore (TVar (Right i)) [a1, a2] ws), "SplitR")
                where
                  a1 = TVar $ Right n
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2

step n (Sub (TVar (Right i)) (TVar (Left j)) : ws)                                        -- 11
  | prec ws (TVar (Left j)) (TVar (Right i))    =
    (n, Right $ updateBoundInWL (TVar (Right i)) (UB, TVar (Left j)) ws, "SolveLVar")
  | otherwise = error "Bug: Incorrect var order in step call!"
step n (Sub (TVar (Left j)) (TVar (Right i))  : ws)                                       -- 12
  | prec ws (TVar (Left j)) (TVar (Right i))    =
    (n, Right $ updateBoundInWL (TVar (Right i)) (LB, TVar (Left j)) ws, "SolveRVar")
  | otherwise                                   =
    error "Bug: Incorrect var order in step call"

step n (Sub (TVar (Right i)) TInt : ws)         =                                         -- 13
  (n, Right $ updateBoundInWL (TVar (Right i)) (UB, TInt) ws, "SolveLInt")
step n (Sub TInt (TVar (Right i)) : ws)         =                                         -- 14
  (n, Right $ updateBoundInWL (TVar (Right i)) (LB, TInt) ws, "SolveRInt")
step n (Sub (TVar (Right i)) TBool : ws)         =                                        -- 13
  (n, Right $ updateBoundInWL (TVar (Right i)) (UB, TBool) ws, "SolveLBool")
step n (Sub TBool (TVar (Right i)) : ws)         =                                        -- 14
  (n, Right $ updateBoundInWL (TVar (Right i)) (LB, TBool) ws, "SolveRBool")

step n (Sub (TVar (Right i)) (TVar (Right j)) : ws)                                       -- 15 & 16
  | prec ws (TVar (Right i)) (TVar (Right j))   =
    (n, Right $ updateBoundInWL (TVar (Right j)) (LB, TVar (Right i)) ws, "SolveLExtVar")
  | prec ws (TVar (Right j)) (TVar (Right i))   =
    (n, Right $ updateBoundInWL (TVar (Right i)) (UB, TVar (Right j)) ws, "SolveRExtVar")

step n _                                        = (n, Left "No matched pattern", "None")


checkAndShow :: Int -> [Work] -> String
checkAndShow n [] = "Success!"
checkAndShow n ws =
  case ws' of
    Left e -> "   " ++ show (reverse ws) ++ "\n-->{Rule : " ++ s1  ++ " }\n" ++ e
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

chkAndShow = putStrLn .  checkAndShow 0

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
ws1 = [Sub ex1 (TArrow TInt (TArrow ex2 ex3)), Sub ex2 (TArrow TInt ex1),  WExVar 2 [] [],  WExVar 1 [] [], WExVar 3 [] []]