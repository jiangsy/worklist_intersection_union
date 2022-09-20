
{-# LANGUAGE LambdaCase, MultiWayIf #-}
module InferLazyIUSet where

import Data.List
import Data.Set.Unordered.Unique as USet (UUSet, insert, empty, unUUSet)
import Data.Hashable
import Control.Monad (guard)

import TestCase
import InteractiveEval (back)
import Data.Set.Unordered.Many (UMSet(unUMSet))

{- A lazy subtyping algorithm with union and intersection:

A,B := a | ^a | Int | A -> B | forall a. A | A ∪ B | A ∩ B | ⊤
      | ⊥

t := a | ^a | t1 -> t2 | t1 ∪ t2 | t1 ∩ t2

T ::= . | T, a | T, t1<:^a<:t2 | T, A <: B

Algorithm:

|- T 
------------------------------
|- T , a

|- T , t1 <: t2
------------------------------
|- T , t1 <: ^a <: t1 

|- T 
------------------------------
|- T , Int <: Int  

|- T  /\  a in T
------------------------------
|- T , a <: a

|- T  /\  ^a in T
------------------------------
|- T , ^a <: ^a

|- T, C <: A |- B <: D
------------------------------
|- T , A -> B <: C -> D  

|- T, A <: C 
-----------------
|- T, A & B <: C 

|- T, B <: C 
-----------------
|- T, A & B <: C 

|- T, C <: A |- C <: B
-----------------
|- T, C <: A & B

|- T, A <: C |- B <: C
-----------------
|- T, A ∪ B <: C 

|- T, C <: A
-----------------
|- T, C <: A ∪ B

|- T, C <: B
-----------------
|- T, C <: A ∪ B

|- T, ⊥<:^a<:⊤, [^a/a] B 
------------------------
|- T, forall a . B <: C            

|- T, b, A <: C           
-----------------------
|- T, A <: forall b . B            

|- ([^a1->^a2 /+ ^a]_[] (T, ^a1, ^a2)), ^a1->^a2 <: A->B   /\ not monotype (A->B)  
---------------------------------------------------------------------------------------
|- T, ^a <: A->B 

|- ([^a1->^a2 /- ^a]_[] (T, ^a1, ^a2)), A->B <: ^a1->^a2   /\ not monotype (A->B)  
---------------------------------------------------------------------------------------
|- T, A->B <: ^a 

|- ([t /- ^a]_[] T)
-----------------------------
|- T, t<:^a  

|- ([t /+ ^a]_[] T) 
-----------------------------
|- T, ^a<:t

|- ([^b /- ^a]_[] T) /\ ^b in front of ^a
-----------------------------
|- T, ^b<:^a

|- ([^b /+ ^a]_[] T) /\ ^b in front of ^a
-----------------------------
|- T, a^<:^b

--------------
[A /* ^a]_E T
--------------

[A /- ^a]_E (T, t1<:^a<:t2)   = T, reverse E, L∪A<:^a<: R        ^a notin FV(A + E)
[A /+ ^a]_E (T, t1<:^a<:t2)   = T, reverse E, L<:^a<:R∩A         ^a notin FV(A + E)

[A /* ^a]_E (T, t1<:^b<:t2)   = [A /* ^a]_E T, t1<:^b<:t2        ^b notin FV(A + E)
[A /* ^a]_E (T, t1<:^b<:t2)   = [A /* ^a]_{E, t1<:^b<:t2} T      (^b in  FV(A + E)) and ^a notin (L+R)
[A /* ^a]_E (T, a)            = [A /* ^a]_{E} T, a               a notin FV(A+ E) 
[A /* ^a]_E (|- T, B <: C)    = [A /* ^a]_{E} T, B <: C       

-}


data Typ = TVar (Either Int Int) | TInt | TBool | TForall (Typ -> Typ) | TArrow Typ Typ | TUnion (UUSet Typ) |
    TIntersection (UUSet Typ)

data Work = WVar Int | WExVar Int Typ Typ | Sub Typ Typ deriving Eq

data BoundTyp = LB | UB

ppTyp :: Int -> Typ -> String
ppTyp n (TVar (Left i))       = show i
ppTyp n (TVar (Right i))      = "^" ++ show i
ppTyp n TInt                  = "Int"
ppTyp n TBool                 = "Bool"
ppTyp n (TArrow a b)          = "(" ++ ppTyp n a ++ ") -> " ++ ppTyp n b
ppTyp n (TForall f)           = "forall " ++ show n ++ ". " ++ "(" ++ ppTyp (n+1) (f (TVar (Left n))) ++ ")"
ppTyp n (TUnion t_set)        = intercalate "∪" (map (ppTyp n) (toList t_set))
ppTyp n (TIntersection t_set) = intercalate "∩" (map (ppTyp n) (toList t_set))


eqTyp :: Int -> Typ -> Typ -> Bool
eqTyp n TInt TInt                                     = True
eqTyp n TBool TBool                                   = True
eqTyp n (TVar v1) (TVar v2)                           = v1 == v2
eqTyp n (TArrow a b) (TArrow c d)                     = a == c && b == d
eqTyp n (TForall g) (TForall h)                       = eqTyp (n+1) (g (TVar (Left n))) (h (TVar (Left n)))
eqTyp n (TUnion tSet1) (TUnion tSet2)                 = tSet1 == tSet2
eqTyp n (TIntersection tSet1) (TIntersection tSet2)   = tSet1 == tSet2
eqTyp n _ _                                           = False


instance Eq Typ where
  t1 == t2 = eqTyp 0 t1 t2

instance Show Typ where
  show = ppTyp 0

instance Show Work where
  show (WVar i)   = show i
  show (WExVar i lbs ubs)  = show lbs ++ " <: " ++ "^" ++ show i ++ " <: " ++ show ubs
  show (Sub a b)      = show a ++ " <: " ++ show b

toList :: Eq a => UUSet a -> [a]
toList = unUUSet

{- A lazy subtyping algorithm:

A,B := a | ^a | Int | A -> B | forall a. A | 
T ::= . | T,a | T, lbs <: ^a <: ubs |- A <: B

Algorithm:

[#splits, #forall, #existential, |wl|]

(3 * #splits + #forall + #existential, |wl|)

01. T, a                               --> T                                                      (rule 1)
[0, 0, 0, -1] -> (0, -1)

02. T[^a] |- [l1..ln] <: ^a <:[u1..um] --> |- T, l1 <: u1 .... |- ln <: lm (n x m)                 (rule 2)
[0, 0, -1, +(n*m-1)] -> (-1, +?)

03. |- T, Int <: Int                    --> T                                                      (rule 5)
[0, 0, 0, -1] -> (0, -1)

04. T[a]  |- a <: a                    --> T                                                      (rule 6)
[0, 0, 0, -1] -> (0, -1)

05. T[^a] |- ^a <: ^a                  --> T                                                      (rule 7)
[0, 0, 0, -1] -> (0, -1)

06. |- T, A -> B <: C -> D              --> |- T, C <: A |- B <: D                                  (rule 8)
[0, 0, 0, -2] -> (0, -2)

07. |- T, forall a . B <: C             --> T,^a |- [^a/a] B <: C                                  (rule 9)
[0, -1, +1, -1] -> (0, -1)

08. |- T, A <: forall b . B             --> T,b |- A <: C                                          (rule 10)
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
[A/^a]_E (|- T, B <: C)      = [A/^a]_(E, B <: C) T             fv(B + C) ∩ fv(A + E) != Φ
[A/^a]_E (|- T, B <: C)      = [A/^a]_(E) (|- T, B <: C)         fv(B + C) ∩ fv(A + E) = Φ

-}


mono :: Typ -> Bool
mono (TForall g)       = False
mono (TArrow a b)      = mono a && mono b
mono (TUnion _)        = True
mono (TIntersection _) = True
mono _                 = True

fv :: Typ -> [Typ]
fv (TVar i)               = [TVar i]
fv (TArrow t1 t2)         = fv t1 `union` fv t2
fv (TForall g)            = fv (g TInt)
fv (TUnion t_set)         = nub (concatMap fv (toList t_set))
fv (TIntersection t_set)  = nub (concatMap fv (toList t_set))
fv _                      = []

fvInWork :: Work -> [Typ]
fvInWork (WVar i)         = []
fvInWork (WExVar j lb ub) = fv lb `union` fv ub
fvInWork (Sub t1 t2)      = fv t1 `union` fv t2

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
updateBoundInWL var@(TVar (Right i)) bound (WExVar j lb@(TUnion tSet1) ub@(TIntersection tSet2) : ws)
  | i == j =
      case bound of
        (LB, typ) -> if var `elem` fVars then Left $  "Error: Cyclic Dependency of " ++ show var ++ " self!"  else Right $ WExVar j (TUnion $ USet.insert typ tSet1) ub : ws
          where fVars = nub $ fv typ
        (UB, typ) -> if var `elem` fVars then Left $  "Error: Cyclic Dependency of " ++ show var ++ " self!" else Right $ WExVar j lb (TIntersection $ USet.insert typ tSet2) : ws
          where fVars = nub $ fv typ
  | otherwise = updateBoundInWL var bound ws >>= (\ws' -> Right $ WExVar j lb ub : ws')
updateBoundInWL var bound (w:ws) = updateBoundInWL var bound ws >>= (\ws' -> Right $ w : ws')
updateBoundInWL var bound [] = error "Bug: Var not found!"

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


emptyLB = TUnion empty
emptyUB = TIntersection empty

step :: Int -> [Work] -> (Int, Either String [Work], String)
step n (WVar i : ws)                            = (n, Right ws, "Garbage Collection")     -- 01 
step n (WExVar i lb ub : ws)                    = (n, Right $Sub lb ub : ws, "SCompareBound")

step n (Sub TInt TInt : ws)                     = (n, Right ws, "SInt")                   -- 03
step n (Sub TBool TBool : ws)                   = (n, Right ws, "SBool")                  -- 03

step n (Sub (TVar i) (TVar j) : ws)| i == j     = (n, Right ws, "SUVar")                  -- 04 + 05
step n (Sub (TArrow a b) (TArrow c d) : ws)     =                                         -- 06
  (n, Right $  Sub b d : Sub c a : ws, "SArrow")

step n (Sub a (TForall g) : ws)                 =                                         -- 08
  (n+1, Right $ Sub a (g (TVar (Left n))) : WVar n : ws, "SForallR")
step n (Sub (TForall g) b : ws)                 =                                         -- 07
  (n+1, Right $  Sub (g (TVar (Right n))) b : WExVar n emptyLB emptyUB : ws, "SForallL")


step n (Sub (TVar (Right i)) (TArrow a b) : ws)                                           -- 09
   | not $ mono (TArrow a b)                    =
    (n+2, carryBackInWL (TVar (Right i)) a1_a2 (Sub a1_a2 (TArrow a b) :
                                                WExVar (n+1) emptyLB emptyUB :
                                                WExVar n emptyLB emptyUB : ws) >>=
      updateBoundInWL (TVar (Right i)) (UB, a1_a2), "SplitL")
                where
                  a1 = TVar (Right n)
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2

step n (Sub (TArrow a b) (TVar (Right i)) : ws)                                           -- 09
   | not $ mono (TArrow a b)                    =
    (n+2, carryBackInWL (TVar (Right i)) a1_a2 (Sub (TArrow a b) a1_a2 :
                                                WExVar (n+1) emptyLB emptyUB :
                                                WExVar n emptyLB emptyUB : ws) >>=
      updateBoundInWL (TVar (Right i)) (LB, a1_a2), "SplitL")
                where
                  a1 = TVar (Right n)
                  a2 = TVar $ Right (n + 1)
                  a1_a2 = TArrow a1 a2

step n (Sub vi@(TVar (Right i)) vj@(TVar (Right j)) : ws)                                       -- 15 & 16
  | prec ws vi vj                               =
    (n, carryBackInWL vj vi ws >>= updateBoundInWL vj (UB, vi), "SolveLExtVar")
  | prec ws vj vi                               =
    (n, carryBackInWL vi vj ws >>= updateBoundInWL vi (UB, vj), "SolveRExtVar")

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



curInfo :: [Work] -> String -> String
curInfo ws s1 =  "   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ replicate (20 - length s1) ' ' ++ "Size: " ++ show (size ws) ++ " }\n"

bigStep :: Int -> String -> [Work] -> (Bool, String)
bigStep _ info []                                   = (True, info)
bigStep n info (WVar i : ws)                        = bigStep n (info ++ curInfo ws "Garbage Collection") ws
bigStep n info (WExVar i lb ub : ws)                = bigStep n (info ++ curInfo ws "SCompareBound") (Sub lb ub : ws)

bigStep n info (Sub TInt TInt : ws)                 = bigStep n (info ++ curInfo ws "SInt") ws
bigStep n info (Sub TBool TBool : ws)               = bigStep n (info ++ curInfo ws "SBool") ws


bigStep n info (Sub (TVar i) (TVar j) : ws )
                         | i == j                   = bigStep n (info ++ curInfo ws "STVar") ws
bigStep n info (Sub (TArrow a b) (TArrow c d) : ws) = bigStep n (info ++ curInfo ws "SArrow") (Sub b d : Sub c a : ws)
bigStep n info (Sub a (TForall g) : ws)             = bigStep (n+1) (info ++ curInfo ws "SFroallR") (Sub a (g (TVar (Left n))) : WVar n : ws)
bigStep n info (Sub (TForall g) b : ws)             = bigStep (n+1) (info ++ curInfo ws "SForallL") (Sub (g (TVar (Right n))) b: WExVar n emptyLB emptyUB : ws)


bigStep n info (Sub (TVar (Right i)) (TArrow a b) : ws)
  | not $ mono (TArrow a b)                         = case carryBackInWL (TVar (Right i)) a1_a2 (Sub a1_a2 (TArrow a b) :
                                                                                                 WExVar (n+1) emptyLB emptyUB : WExVar n emptyLB emptyUB : ws) 
                                                           >>= updateBoundInWL (TVar (Right i)) (UB, a1_a2) of
                                                        Left error -> (False, info++error)
                                                        Right ws' -> bigStep (n+2) (info ++ curInfo ws "SplitL") ws'
                           where
                             a1 = TVar (Right n)
                             a2 = TVar $ Right (n + 1)
                             a1_a2 = TArrow a1 a2
bigStep n info (Sub (TArrow a b) (TVar (Right i)) : ws) 
  | not $ mono (TArrow a b)                         = case carryBackInWL (TVar (Right i)) a1_a2 (Sub (TArrow a b) a1_a2 :
                                                                                                 WExVar (n+1) emptyLB emptyUB :
                                                                                                 WExVar n emptyLB emptyUB : ws) 
                                                          >>= updateBoundInWL (TVar (Right i)) (LB, a1_a2) of
                                                        Left error -> (False, info ++ error)
                                                        Right ws' -> bigStep (n+1) (info ++ curInfo ws "SplitR") ws'
                           where
                             a1 = TVar (Right n)
                             a2 = TVar $ Right (n + 1)
                             a1_a2 = TArrow a1 a2

bigStep n info (Sub vi@(TVar (Right i)) vj@(TVar (Right j)) : ws)                                       -- 15 & 16
  | prec ws vi vj                                   = case carryBackInWL vj vi ws >>= updateBoundInWL vj (UB, vi) of 
                                                        Left error -> (False, info ++ error)
                                                        Right ws' -> bigStep n (info++curInfo ws "SolveLExtVar") ws'
  | prec ws vj vi                                   = case carryBackInWL vi vj ws >>= updateBoundInWL vi (UB, vj) of 
                                                        Left error -> (False, info ++ error)
                                                        Right ws' -> bigStep n (info++curInfo ws "SolveRExtVar") ws'

bigStep n info (Sub (TVar (Right i)) t : ws)                                        -- 11
  | mono t                                          = case carryBackInWL (TVar (Right i)) t ws >>= 
                                                          updateBoundInWL (TVar (Right i)) (UB, t) of
                                                        Left error -> (False, info ++ error)
                                                        Right ws' -> bigStep n (info++curInfo ws "SolveMonoL") ws'

bigStep n info (Sub t (TVar (Right i))  : ws)                                       -- 12
  | mono t                                          = case carryBackInWL (TVar (Right i)) t ws >>=
                                                          updateBoundInWL (TVar (Right i)) (LB, t) of 
                                                        Left error -> (False, info++error)
                                                        Right ws' -> bigStep n (info++curInfo ws "SolveMonoR") ws'

bigStep n info (Sub t1 (TIntersection tSet2) : ws) = bigStep n (info ++ curInfo ws "SIntersection") ([Sub t1 t2 | t2 <- toList tSet2] ++ ws)
bigStep n info (Sub (TIntersection tSet1) t2 : ws) = tryPath $ toList tSet1
    where tryPath (t1 : ts1) = case bigStep n info (Sub t1 t2 : ws) of
                                (True, info) -> (True, info)
                                (False, s) -> tryPath ts1
          tryPath []         = (False, info)

bigStep n info (Sub (TUnion tSet1) t2 : ws)        = bigStep n (info ++ curInfo ws "SUnion") ([Sub t1 t2| t1 <- toList tSet1] ++ ws)
bigStep n info (Sub t1 (TUnion tSet2) : ws)        = tryPath (toList tSet2)
    where
        tryPath (t2 : ts2) = case bigStep n info (Sub t1 t2 : ws) of
                                (True, info) -> (True, info)
                                (False, s) -> tryPath ts2
        tryPath []       = (False, info)

bigStep _ info _                                 = (False, info)

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

