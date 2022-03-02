{-# LANGUAGE LambdaCase #-}
import Data.List

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
10. T[lbs <: ^a < ubs] |- A -> B <: ^a --> T[^a1,^a2, lbs U {^a1,^a2} <: ^a < ubs] |- A -> B <: ^a1 -> ^a2   

11. T[a][lbs <: ^b < ubs] |- a <: ^b   --> T[a][lbs U {a} <: ^b < ub] 
12. T[a][lbs <: ^b < ubs] |- ^b <: a   --> T[a][lbs <: ^b < ub U {a}] 
13. T[lbs <: ^b < ubs] |- Int <: ^b    --> T[a][lbs U {Int} <: ^b < ub] 
14. T[lbs <: ^b < ubs] |- ^b <: Int    --> T[a][lb s<: ^b < ub U {Int}] 

15. T[^a][lbs <: ^b < ubs] |- ^a <: ^b --> T[^a][lb U {^a} <: ^b < ub] 
16. T[^a][lbs <: ^b < ubs] |- ^b <: ^a --> T[^a][lb <: ^b < ub U {^a}] 

-}
fv :: Typ -> [Int]
fv (TVar (Right i)) = [i]
fv (TArrow t1 t2)   = fv t1 `union` fv t2
fv (TForall g)      = fv (g TInt)
fv _                = []

updateBoundWL :: Typ -> (BoundTyp, Typ) -> [Work] -> [Work]
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


-- var a appears before var b in the worklist => var a appears in the sub-worklist starting from var b

wsToVars :: [Work] -> [Either Int Int]
wsToVars = concatMap ( \case
                       WVar i -> [Left i]
                       WExVar i _ _-> [Right i]
                       _   -> []
                     )

getVarsBeforeTyp :: [Work] -> Typ -> [Typ]
getVarsBeforeTyp wl (TVar i) = map TVar $ dropWhile (/= i) $ wsToVars wl
getVarsBeforeTyp wl x = error (show x ++ "is not a type")

getVarsAfterTyp :: [Work] -> Typ -> [Typ]
getVarsAfterTyp wl (TVar i) = map TVar $ takeWhile (/= i) $ wsToVars wl
getVarsAfterTyp wl x = error (show x ++ "is not a type")

-- var a appears before var b in the worklist => var a appears in the sub-worklist starting from var b
prec :: [Work] -> Typ -> Typ -> Bool
prec wl varA varB = varA `elem` getVarsBeforeTyp wl varB


step :: Int -> [Work] -> (Int, Either String [Work], String)
step n (WVar i : ws)                            = (n, Right ws, "Garbage Collection")     -- 01 
step n (WExVar i lbs ubs : ws)                  =                                   -- 02
  (n, Right $ [Sub lTyp uTyp | lTyp <- lbs, uTyp <- ubs] ++ ws, "SUnfoldBounds")
step n (Sub TInt TInt : ws)                     = (n, Right ws, "SInt")                   -- 03
step n (Sub (TVar i) (TVar j) : ws)| i == j     = (n, Right ws, "SUVar")                  -- 04 + 05
step n (Sub (TArrow a b) (TArrow c d) : ws)     =                                   -- 06
  (n, Right $ Sub b d : Sub c a : ws, "SArrow")

step n (Sub a (TForall g) : ws)                 =                                   -- 08
  (n+1, Right $ Sub a (g (TVar (Left n))) : WVar n : ws, "SForallR")
step n (Sub (TForall g) b : ws)                 =                                   -- 07
  (n+1, Right $ Sub (g (TVar (Right n))) b : WExVar n [] [] : ws, "SForallL")


step n (Sub (TVar (Right i)) (TArrow a b) : ws) =                                   -- 09
  (n+2, Right $ Sub (TArrow a1 a2) (TArrow a b) : updateBoundWL (TVar (Right i)) (UB, a1_a2) (addTypsBefore (TVar (Right i)) [a1, a2] ws), "SplitL")
  where
    a1 = TVar (Right n)
    a2 = TVar $ Right (n + 1)
    a1_a2 = TArrow a1 a2
step n (Sub (TArrow a b) (TVar (Right i)) : ws) =                                   -- 10
  (n+2,  Right $ Sub (TArrow a b) (TArrow a1 a2) : updateBoundWL (TVar (Right i)) (LB, a1_a2) (addTypsBefore (TVar (Right i)) [a1, a2] ws), "SplitR")
  where
    a1 = TVar $ Right n
    a2 = TVar $ Right (n + 1)
    a1_a2 = TArrow a1 a2

step n (Sub (TVar (Right i)) (TVar (Left j)) : ws)                                  -- 11
  | prec ws (TVar (Left j)) (TVar (Right i))    = 
      (n, Right $ updateBoundWL (TVar (Right i)) (UB, TVar (Left j)) ws, "SolveLVar")
  | otherwise = error "Bug: Incorrect var order in step call"
step n (Sub (TVar (Left j)) (TVar (Right i))  : ws)                                 -- 12
  | prec ws (TVar (Left j)) (TVar (Right i))    =
     (n, Right $ updateBoundWL (TVar (Right i)) (LB, TVar (Left j)) ws, "SolveRVar")
  | otherwise = error "Bug: Incorrect var order in step call"

step n (Sub (TVar (Right i)) TInt : ws)         =                                   -- 13
  (n, Right $ updateBoundWL (TVar (Right i)) (UB, TInt) ws, "SolveLInt")
step n (Sub TInt (TVar (Right i)) : ws)         =                                   -- 14
  (n, Right $ updateBoundWL (TVar (Right i)) (LB, TInt) ws, "SolveRInt")
step n (Sub (TVar (Right i)) (TVar (Right j)) : ws)                                 -- 15 & 16
  | prec ws (TVar (Right i)) (TVar (Right j))   = 
    (n, Right $ updateBoundWL (TVar (Right j)) (LB, TVar (Right i)) ws, "SolveLExtVar")
  | prec ws (TVar (Right j)) (TVar (Right i))   = 
    (n, Right $ updateBoundWL (TVar (Right i)) (UB, TVar (Right j)) ws, "SolveRExtVar")

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

test10 = chkAndShow [WExVar 4 [TVar (Right 2)] [TArrow (TVar (Right 1)) TInt], WExVar 3 [TVar (Right 1)] [TArrow (TVar (Right 2)) TInt], WExVar 2 [] [], WExVar 1 [] []]