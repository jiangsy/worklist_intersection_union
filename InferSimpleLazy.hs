import Prelude hiding (flip)
import Data.List
-- import Data.Set as Set

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
10. T[lbs <: ^a < ubs] |- A -> B <: ^a --> T[^a1,^a2, lbs U {^a1,^a2} <: ^a < ubs] |- A -> B <: ^a1 -> ^a2   
                when not monotype (A->B)  

11. T[a][lbs <: ^b < ubs] |- a <: ^b   --> T[a][lbs U {a} <: ^b < ub] 
12. T[a][lbs <: ^b < ubs] |- ^b <: a   --> T[a][lbs <: ^b < ub U {a}] 
13. T[lbs <: ^b < ubs] |- Int <: ^b    --> T[a][lbs U {Int} <: ^b < ub] 
14. T[lbs <: ^b < ubs] |- ^b <: Int    --> T[a][lb s<: ^b < ub U {Int}] 

15. T[^a][lbs <: ^b < ubs] |- ^a <: ^b --> T[^a][lb U {^a} <: ^b < ub] 
16. T[^a][lbs <: ^b < ubs] |- ^b <: ^a --> T[^a][lb <: ^b < ub U {^a}] 


TODO: Does subst rule need changes?
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
data Work = V (Either Int Int)  | Sub Typ Typ | Constraint Typ [Typ] [Typ] deriving Eq

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
  show (V (Left i))   = show i
  show (V (Right i))  = "^" ++ show i
  show (Sub a b)      = show a ++ " <: " ++ show b
  show (Constraint a lb ub)  = show lb ++  " <: " ++ show a ++ " <: " ++ show ub

instance Eq Typ where
  t1 == t2 = eqTyp 0 t1 t2

mono :: Typ -> Bool
mono (TForall g)  = False
mono (TArrow a b) = mono a && mono b
mono _            = True

subst :: Int -> Typ -> Typ -> Typ
subst i t TInt                    = TInt
subst i t (TVar v)                =
   case v of
     Right j | i == j -> t
     _                -> TVar v
subst i t (TArrow t1 t2)        = TArrow (subst i t t1) (subst i t t2)
subst i t (TForall g)           = TForall (\t1 -> subst i t (g t1))

fv :: Typ -> [Int]
fv (TVar (Right i)) = [i]
fv (TArrow t1 t2)   = fv t1 `union` fv t2
fv (TForall g)      = fv (g TInt)
fv _                = []

substWL :: Int ->  Typ -> [Int] -> [Work] -> [Work]
substWL i t es (Sub t1 t2 : ws) = Sub (subst i t t1) (subst i t t2) : substWL i t es ws
substWL i t es _ = error "Incorrect substWL()!"

updateBoundWL :: Typ -> (Bound, Typ) -> [Work] -> [Work]
-- match once and no more recursion
updateBoundWL var bound oldWL@(Constraint constraint_var lbs ubs : ws)
  | var == constraint_var =
      case bound of
        (LB, typ) -> Constraint constraint_var (typ:lbs) ubs : ws
        (UB, typ) -> Constraint constraint_var lbs (typ:ubs) : ws
  | otherwise = oldWL
updateBoundWL var bound (w:ws) = w : updateBoundWL var bound ws
updateBoundWL var bound [] = []

prec :: [Work] -> Typ -> Typ -> Bool
prec w (TVar a) (TVar b) = elem a . dropWhile (/= b) $ wex
  where
    wex = concatMap (\x -> case x of
        V v -> [v]
        _   -> []
      ) w
prec w _ _ = error "Incorrect prec call!"


step :: Int -> [Work] -> (Int, [Work], String)
step n (V i : ws)                               = (n, ws, "Garbage Collection")     -- 01 
step n (Constraint (TVar (Right i)) lbs ubs : ws)    =                              -- 02
  (n, [Sub lTyp uTyp | lTyp <- lbs, uTyp <- ubs] ++ ws, "SExpandBounds")
step n (Sub TInt TInt : ws)                     = (n, ws, "SInt")                   -- 03
step n (Sub (TVar i) (TVar j) : ws)| i == j     = (n, ws, "SUVar")                  -- 04 + 05
step n (Sub (TArrow a b) (TArrow c d) : ws)     =                                   -- 06
                  (n, Sub b d : Sub c a : ws, "SArrow")
step n (Sub (TForall g) b : ws)                 =                                   -- 07
  (n+1, Sub (g (TVar (Right n))) b : V (Right n) : Constraint (TVar (Right n)) [] [] : ws, "SForallL")
step n (Sub a (TForall g) : ws)                 =                                   -- 08
  (n+1, Sub a (g (TVar (Left n))) : V (Left n) : ws, "SForallR")
-- step n (Sub (TVar (Right i)) (TArrow a b) : ws) =
--    (n+2, Sub a a1 : Sub a2 b : substWL i a1_a2 [n,n+1] ws, "SplitL")
--   where
--     a1 = TVar (Right n)
--     a2 = TVar $ Right (n + 1)
--     a1_a2 = TArrow a1 a2
-- step n (Sub (TArrow a b) (TVar (Right i)) : ws) =
--   (n+2, Sub a1 a : Sub b a2 : substWL i a1_a2 [n,n+1] ws, "SplitR")
--   where
--     a1 = TVar $ Right n
--     a2 = TVar $ Right (n + 1)
--     a1_a2 = TArrow a1 a2
step n (Sub (TVar (Right i)) (TVar (Left j)) : ws)                                  -- 11
  | prec ws (TVar (Left j)) (TVar (Right i))  = (n, updateBoundWL (TVar (Right i)) (UB, TVar (Left j)) ws, "SolveLVar")
  | otherwise = error "Incorrect var order in step call!"
step n (Sub (TVar (Left j)) (TVar (Right i))  : ws)                                 -- 12
  | prec ws (TVar (Left j)) (TVar (Right i)) = (n, updateBoundWL (TVar (Right i)) (LB, TVar (Right i)) ws, "SolveRVar")
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
  in ("   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ " \t\t\t Size: " ++ show (size ws) ++ " }\n" ++ s2)

size :: [Work] -> (Int,Int)
size ws = (measure1 ws, sizeWL ws)

-- Measure 1

measure1 :: [Work] -> Int
measure1 ws = 2 * splits ws + foralls ws + existentials ws

splits []              = 0
splits (V i : ws)      = splits ws
splits (Sub a b : ws)  = splitsSub a b + splits ws

splitsSub :: Typ -> Typ -> Int
splitsSub (TVar (Right i)) t1@(TArrow _ _) = splitsTyp t1
splitsSub t1@(TArrow _ _) (TVar (Right i)) = splitsTyp t1
splitsSub (TArrow a b) (TArrow c d) =
  splitsSub c a + splitsSub b d
splitsSub a (TForall g) = splitsSub a (g (TVar (Left 0)))
splitsSub (TForall g) a = splitsSub (g (TVar (Right 0))) a
splitsSub a b           = 0

splitsTyp (TArrow a b)
  | not (mono a) && not (mono b) = 1 + splitsTyp a + splitsTyp b
  | not (mono a)                 = 1 + splitsTyp a
  | not (mono b)                 = 1 + splitsTyp b
  | otherwise                    = 0
splitsTyp (TForall g)            = splitsTyp (g TInt)
splitsTyp _                      = 0

existentials []                 = 0
existentials (V (Right i) : ws) = 1 + existentials ws
existentials (_ : ws)           = existentials ws

foralls []                      = 0
foralls (V i : ws)              = foralls ws
foralls (Sub a b : ws)          = forallsTyp a + forallsTyp b + foralls ws

forallsTyp (TForall g)  = 1 + forallsTyp (g TInt)
forallsTyp (TArrow a b) = forallsTyp a + forallsTyp b
forallsTyp _            = 0

sizeWL :: [Work] -> Int
sizeWL []              = 0
sizeWL (V i : ws)      = 1 + sizeWL ws
sizeWL (Sub a b : ws)  = sizeSub a b + sizeWL ws

sizeSub (TArrow a b) (TArrow c d) = 2 + sizeSub c a + sizeSub b d
sizeSub (TForall g) a             = 2 + sizeSub (g TInt) a
sizeSub a (TForall g)             = 2 + sizeSub a (g TInt)
sizeSub _ _                       = 1
