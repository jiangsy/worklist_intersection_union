
{-# LANGUAGE LambdaCase, MultiWayIf #-}
module InferLazyIUTree where

import Data.List ( nub, tails, union )

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

|- T 
------------------------------
|- T , t <: Top  

|- T 
------------------------------
|- T , Bot <: t  

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

|- T, ⊥<:^a<:⊤, [^a/a] B <: C
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


data Typ = TVar (Either Int Int) | TInt | TBool | TForall (Typ -> Typ) | TArrow Typ Typ |
           TUnion Typ Typ | TIntersection Typ Typ | TBot | TTop

data Work = WVar Int | WExVar Int Typ Typ | Sub Typ Typ deriving Eq

data BoundTyp = LB | UB

ppTyp :: Int -> Typ -> String
ppTyp n (TVar (Left i))       = show i
ppTyp n (TVar (Right i))      = "^" ++ show i
ppTyp n TInt                  = "Int"
ppTyp n TBool                 = "Bool"
ppTyp n (TArrow a b)          = "(" ++ ppTyp n a ++ ") -> " ++ ppTyp n b
ppTyp n (TForall f)           = "forall " ++ show n ++ ". " ++ "(" ++ ppTyp (n+1) (f (TVar (Left n))) ++ ")"
ppTyp n (TUnion t1 t2)        = ppTyp n t1 ++ " ∪ " ++ ppTyp n t2
ppTyp n (TIntersection t1 t2) = ppTyp n t1 ++ " ∩ " ++ ppTyp n t2
ppTyp n TBot                  = "⊥"
ppTyp n TTop                  = "⊤"


-- here the Eq relation is incorrect, but it does not matter
-- we only care about the Eq between TVar
eqTyp :: Int -> Typ -> Typ -> Bool
eqTyp n TInt TInt                                     = True
eqTyp n TBool TBool                                   = True
eqTyp n (TVar v1) (TVar v2)                           = v1 == v2
eqTyp n (TArrow a b) (TArrow c d)                     = a == c && b == d
eqTyp n (TForall g) (TForall h)                       = eqTyp (n+1) (g (TVar (Left n))) (h (TVar (Left n)))
eqTyp n _ _                                           = False


instance Eq Typ where
  t1 == t2 = eqTyp 0 t1 t2

instance Show Typ where
  show = ppTyp 0

instance Show Work where
  show (WVar i)   = show i
  show (WExVar i lbs ubs)  = show lbs ++ " <: " ++ "^" ++ show i ++ " <: " ++ show ubs
  show (Sub a b)      = show a ++ " <: " ++ show b

mono :: Typ -> Bool
mono (TForall g)           = False
mono TBot                  = False
mono TTop                  = False
mono (TArrow a b)          = mono a && mono b
mono (TUnion a b)          = mono a && mono b
mono (TIntersection a b)   = mono a && mono b
mono _                     = True

fv :: Typ -> [Typ]
fv (TVar i)               = [TVar i]
fv (TArrow t1 t2)         = fv t1 `union` fv t2
fv (TForall g)            = fv (g TInt)
fv (TUnion t1 t2)         = fv t1 `union` fv t2
fv (TIntersection t1 t2)  = fv t1 `union` fv t2
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
updateBoundInWL var@(TVar (Right i)) bound (WExVar j lb ub : ws)
  | i == j =
      case bound of
        (LB, typ) -> if var `elem` fVars then Left $  "Error: Cyclic Dependency of " ++ show var ++ " self!"  else Right $ WExVar j (TUnion typ lb) ub : ws
          where fVars = nub $ fv typ
        (UB, typ) -> if var `elem` fVars then Left $  "Error: Cyclic Dependency of " ++ show var ++ " self!" else Right $ WExVar j lb (TIntersection typ ub) : ws
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



curInfo :: [Work] -> String -> String
curInfo ws s1 =  "   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ replicate (20 - length s1) ' ' ++ "Size: " ++ show (size ws) ++ " }\n"

bigStep :: Int -> String -> [Work] -> (Bool, String)
bigStep _ info []                                   = (True, info)
bigStep n info (WVar i : ws)                        = bigStep n (info++curInfo ws "Garbage Collection") ws
bigStep n info (WExVar i lb ub : ws)                = bigStep n (info++curInfo ws' "SCompareBound") ws'
                                                        where ws' = Sub lb ub : ws

bigStep n info (Sub _ TTop : ws)                    = bigStep n (info++curInfo ws "STop") ws
bigStep n info (Sub TBot _ : ws)                    = bigStep n (info++curInfo ws "SBot") ws
bigStep n info (Sub TInt TInt : ws)                 = bigStep n (info++curInfo ws "SInt") ws
bigStep n info (Sub TBool TBool : ws)               = bigStep n (info++curInfo ws "SBool") ws


bigStep n info (Sub (TVar i) (TVar j) : ws )
                         | i == j                   = bigStep n (info ++ curInfo ws "STVar") ws
bigStep n info (Sub (TArrow a b) (TArrow c d) : ws) = bigStep n (info ++ curInfo ws' "SArrow") ws'
                                                        where ws' = Sub b d : Sub c a : ws
bigStep n info (Sub a (TForall g) : ws)             = bigStep (n+1) (info ++ curInfo ws' "SFroallR") ws'
                                                        where ws' = Sub a (g (TVar (Left n))) : WVar n : ws
bigStep n info (Sub (TForall g) b : ws)             = bigStep (n+1) (info ++ curInfo ws' "SForallL") ws'
                                                        where ws' = Sub (g (TVar (Right n))) b: WExVar n TBot TTop : ws


bigStep n info (Sub (TVar (Right i)) (TArrow a b) : ws)
  | not $ mono (TArrow a b)                         = case carryBackInWL (TVar (Right i)) a1_a2 (Sub a1_a2 (TArrow a b) :
                                                                                                 WExVar (n+1) TBot TTop :
                                                                                                 WExVar n TBot TTop : ws)
                                                           >>= updateBoundInWL (TVar (Right i)) (UB, a1_a2) of
                                                        Left error -> (False, info++error)
                                                        Right ws' -> bigStep (n+2) (info ++ curInfo ws' "SplitL") ws'
                                                      where
                                                        a1 = TVar (Right n)
                                                        a2 = TVar $ Right (n + 1)
                                                        a1_a2 = TArrow a1 a2
bigStep n info (Sub (TArrow a b) (TVar (Right i)) : ws)
  | not $ mono (TArrow a b)                         = case carryBackInWL (TVar (Right i)) a1_a2 (Sub (TArrow a b) a1_a2 :
                                                                                                 WExVar (n+1) TBot TTop :
                                                                                                 WExVar n TBot TTop : ws)
                                                          >>= updateBoundInWL (TVar (Right i)) (LB, a1_a2) of
                                                        Left error -> (False, info ++ error)
                                                        Right ws' -> bigStep (n+1) (info ++ curInfo ws' "SplitR") ws'
                                                      where
                                                        a1 = TVar (Right n)
                                                        a2 = TVar $ Right (n + 1)
                                                        a1_a2 = TArrow a1 a2

bigStep n info (Sub vi@(TVar (Right i)) vj@(TVar (Right j)) : ws)                                       -- 15 & 16
  | prec ws vi vj                                   = case carryBackInWL vj vi ws >>= updateBoundInWL vj (UB, vi) of
                                                        Left error -> (False, info++error)
                                                        Right ws' -> bigStep n (info++curInfo ws' "SolveLExtVar") ws'
  | prec ws vj vi                                   = case carryBackInWL vi vj ws >>= updateBoundInWL vi (UB, vj) of
                                                        Left error -> (False, info ++ error)
                                                        Right ws' -> bigStep n (info++curInfo ws' "SolveRExtVar") ws'

bigStep n info (Sub (TVar (Right i)) t : ws)                                        -- 11
  | mono t                                          = case carryBackInWL (TVar (Right i)) t ws >>=
                                                          updateBoundInWL (TVar (Right i)) (UB, t) of
                                                        Left error -> (False, info ++ error)
                                                        Right ws' -> bigStep n (info++curInfo ws' "SolveMonoL") ws'

bigStep n info (Sub t (TVar (Right i))  : ws)                                       -- 12
  | mono t                                          = case carryBackInWL (TVar (Right i)) t ws >>=
                                                          updateBoundInWL (TVar (Right i)) (LB, t) of
                                                        Left error -> (False, info++error)
                                                        Right ws' -> bigStep n (info++curInfo ws' "SolveMonoR") ws'

bigStep n info (Sub t1 (TIntersection t21 t22) : ws) = bigStep n (info ++ curInfo ws' "SIntersection") ws'
                                                          where ws' = Sub t1 t21 : Sub t1 t22 : ws
bigStep n info (Sub (TIntersection t11 t12) t2 : ws) = case bigStep n info (Sub t11 t2 : ws) of
                                                          (True, info) -> (True, info++curInfo (Sub t11 t2 : ws) "SIntersection")
                                                          (False, info) -> bigStep n (info ++ curInfo (Sub t12 t2 : ws) "SIntersection") (Sub t12 t2 : ws)

bigStep n info (Sub (TUnion t11 t12) t2 : ws)        = bigStep n (info ++ curInfo ws' "SUnion") ws'
                                                          where ws' = Sub t11 t2 : Sub t12 t2 : ws
bigStep n info (Sub t1 (TUnion t21 t22) : ws)        = case bigStep n info (Sub t1 t21 : ws) of
                                                          (True, info) -> (True, info++curInfo (Sub t1 t21 : ws) "SUnion")
                                                          (False, s) -> bigStep n (info++curInfo (Sub t1 t22 : ws) "SUnion") (Sub t1 t22 : ws)

bigStep _ info _                                     = (False, info)


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

wl1 = [Sub (TForall $ \t -> TArrow t t) (TArrow TInt TBool)]
wl2 = [Sub (TForall $ \t -> TArrow t t) (TArrow TInt (TIntersection TBool TInt))]
wl3 = [Sub (TForall $ \t -> TArrow t t) (TArrow (TIntersection TBool TInt) TInt)]

chkAndShow wl =
  do
    print status
    putStrLn info

  where (status, info) = bigStep 0 "" wl