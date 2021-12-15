module InferSimple where

import Control.Exception
import Prelude hiding (flip)
import Data.List

import Debug.Trace

{- A revised ICFP algorithm:

A,B := Int | A -> B | forall a. A 
T ::= . | T,a | T,^a | T |- A <: B

Algorithm:

[#splits, #forall, #ext, |wl|]

01. T, a                         --> T 
[0, 0, 0, -1] -> (0, -1)

02. T, ^a                        --> T                                                     
[0, 0, -1, -1] -> (-1, -1)

03. T |- Int <: Int              --> T         
[0, 0, 0, -1] -> (0, -1)

04. T[a]  |- a <: a              --> T                                                     
[0, 0, 0, -1] -> (0, -1)

05. T[^a] |- ^a <: ^a            --> T                                                     
[0, 0, 0, -1] -> (0, -1)

06. T |- A -> B <: C -> D        --> T |- C <: A |- B <: D                                 
[0, 0, 0, -1] -> (0, -1) 

07. T |- A <: forall b . B       --> T,b |- A <: C                                         
[0, 0, -1, -1] -> (-1, -1)

08. T |- forall a . B <: C       --> T,^a |- [^a/a] B <: C     
[0, -1, +1, -1] -> (-1, -1)

09. T |- ^a <: t                 --> [t/^a]_{} T        
[0, 0, -1, -2] -> (-1, -2)

10. T |- t <: ^a                 --> [t/^a]_{} T     
[0, 0, -1, -2] -> (-1, -2)

11. T |- ^a <: A -> B            --> [^a1 -> ^a2/^a]_{^a1,^a2} T |- ^a1 -> ^a2 <: A -> B   
       when not monotype (A->B)  
[-1 or more, 0, +1, +?]

12. T |- A -> B <: ^a            --> [^a1 -> ^a2/^a]_{^a1,^a2} T |- A -> B <: ^a1 -> ^a2   
       when not monotype (A->B)  
[-1 or more, 0, +1, +?]

--------------
[A/^a]_E T
--------------

[A/^a]_E (T,^a)             = T,E                 ^a notin fv(A)
[A/^a]_E (T,^b)             = [A/^a]_E T,^b       ^b notin FV(A)
[A/^a]_E (T,^b)             = [A/^a]_{E,^b} T     ^b in FV(A)
[A/^a]_E (T |- B <: C)      = [A/^a]_E T |- [A/^a] B <: [A/^a] C

Concerns:

The system is non-deterministic when the substituted monotype is ^a

Size Measures:

The size measures are a 2 element tuple where the measures have decreasing importance
as follows:

Measure 1 (always decreasing): number of existentials < splits * 2 + foralls + existentials in worklist

Measure 2 (size of worklist, decreases in the first 8 rules, only increases when the measure 1 decreases)

Alternative algorithm with explicit substitutions:

S | T |- ^a <: t                 --> S + (S . t)/^a | T

Int/^b,Int/^a --> ok

Int->Int/^a,Int/^a --> fail

T |- 

-}

data Typ = TVar (Either Int Int) | TInt | TBool | TForall (Typ -> Typ) | TArrow Typ Typ

data Work = V (Either Int Int) | Sub Typ Typ deriving Eq

ppTyp :: Int -> Typ -> String
ppTyp n (TVar (Left i))  = show i
ppTyp n (TVar (Right i)) = "^" ++ show i
ppTyp n TInt             = "Int"
ppTyp n TBool            = "Bool"
ppTyp n (TArrow a b)     = "(" ++ ppTyp n a ++ ") -> " ++ ppTyp n b
ppTyp n (TForall f)      = "forall " ++ show n ++ ". " ++ ppTyp (n+1) (f (TVar (Left n)))  

eqTyp :: Int -> Typ -> Typ -> Bool
eqTyp n TInt TInt = True
eqTyp n TBool TBool = True
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

instance Eq Typ where
  t1 == t2 = eqTyp 0 t1 t2

mono :: Typ -> Bool
mono (TForall g)  = False
mono (TArrow a b) = mono a && mono b
mono _            = True

t1 = TForall (\a -> TArrow a a)

t2 = TArrow t1 (TForall (\a -> TArrow a a))

t3 = TArrow TInt TInt

subst :: Int -> Typ -> Typ -> Typ
subst i t TInt                    = TInt
subst i t TBool                   = TBool
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
substWL i t es (V (Right j) : ws)
   | i == j        = if (not (elem i (fv t))) then map (V . Right) es ++ ws else error (show i ++ " in " ++ show t)
   | elem j (fv t) = substWL i t (j : es) ws
   | otherwise     = V (Right j) : substWL i t es ws
substWL i t es (Sub t1 t2 : ws) = Sub (subst i t t1) (subst i t t2) : substWL i t es ws
substWL _ _ _ _ = error "Error in substWL"

step :: Int -> [Work] -> (Int, Either String [Work], String)
step n (V i : ws)                           = (n, Right ws, "Garbage Collection")     
step n (Sub TInt TInt : ws)                 = (n, Right ws, "SInt") 
step n (Sub TBool TBool : ws)               = (n, Right ws, "SBool")              
step n (Sub (TVar i) (TVar j) : ws)                             -- TODO: need to check if defined
                  | i == j                  = (n, Right ws, "SUVar")                  
step n (Sub (TArrow a b) (TArrow c d) : ws) =
                  (n, Right $ Sub b d : Sub c a : ws, "SArrow")         
step n (Sub a (TForall g) : ws)             =                               
  (n+1, Right $ Sub a (g (TVar (Left n))) : V (Left n) : ws, "SForallR")
step n (Sub (TForall g) b : ws)             =                               
  (n+1, Right $ Sub (g (TVar (Right n))) b : V (Right n) : ws, "SForallL") 
step n (Sub (TVar (Right i)) a  : ws)       
  | mono a                                  = (n, Right $ substWL i a [] ws, "SolveL")
step n (Sub a (TVar (Right i))  : ws)       
  | mono a                                  = (n, Right $ substWL i a [] ws, "SolveL")
step n (Sub (TVar (Right i)) (TArrow a b) : ws) 
                                            = (n + 2, Right $ Sub a a1 : Sub a2 b : substWL i a1_a2 [n,n+1] ws, "SplitL")
  where
    a1 = TVar (Right n)
    a2 = TVar $ Right (n + 1)
    a1_a2 = TArrow a1 a2
step n (Sub (TArrow a b) (TVar (Right i)) : ws) 
                                            = (n + 2, Right $ Sub a1 a : Sub b a2 : substWL i a1_a2 [n,n+1] ws, "SplitR")   
  where
    a1 = TVar $ Right n
    a2 = TVar $ Right (n + 1)
    a1_a2 = TArrow a1 a2
step n _                                    = (n, Left "No matched pattern", "None")

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

-- failing case 20200810
test8 = chk [Sub (TForall $ \a -> TArrow a a) (TArrow t5 (TArrow TInt TInt))]

tEx = TVar . Right

ex1 = tEx 1
ex2 = tEx 2

test9 = putStrLn  $
  check 4 [Sub ex1 (TArrow TInt ex2), Sub ex2 (TArrow TInt ex1), V (Right 2), V (Right 1)]


-- SIZES

-- number of splits, ws, size

size :: [Work] -> (Int,Int)
size ws = (measure1 ws, sizeWL ws)

-- Measure 1

measure1 :: [Work] -> Int
measure1 ws = 2 * splits ws + foralls ws + existentials ws

splits :: [Work] -> Int
splits []              = 0
splits (V i : ws)      = splits ws
splits (Sub a b : ws)  = splitsSub a b + splits ws

splitsSub :: Typ -> Typ -> Int
splitsSub (TVar (Right i)) t1@(TArrow _ _) = splitsTyp t1
splitsSub t1@(TArrow _ _) (TVar (Right i)) = splitsTyp t1
splitsSub (TArrow a b) (TArrow c d)        =
  splitsSub c a + splitsSub b d
splitsSub a (TForall g)                    = splitsSub a (g (TVar (Left 0)))
splitsSub (TForall g) a                    = splitsSub (g (TVar (Right 0))) a
splitsSub a b                              = 0

splitsTyp :: Num a => Typ -> a
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

{-

[Int -> forall a. ^b <: ^c, ^c <: Int -> Int]

-}

-- Measure 2

sizeWL :: [Work] -> Int
sizeWL []              = 0
sizeWL (V i : ws)      = 1 + sizeWL ws
sizeWL (Sub a b : ws)  = sizeSub a b + sizeWL ws

sizeSub (TArrow a b) (TArrow c d) = 2 + sizeSub c a + sizeSub b d
sizeSub (TForall g) a             = 2 + sizeSub (g TInt) a
sizeSub a (TForall g)             = 2 + sizeSub a (g TInt)
sizeSub _ _                       = 1


ex0 = TVar (Right 0)

jimmy = putStrLn $ check 3 [
  Sub TInt TInt,
  Sub ex0 (TArrow TInt TInt),
  Sub (TArrow ex0 (TArrow ex0 $ TForall $ \a -> a)) ex1,
  V (Right 0),
  V (Right 1),
  V (Right 2)
  ]


{-


TopLike B
---------
A <: B

^a, ^a <: Int -> Int, ^a <: Bot -> Top
-->{delete top-like}
^a, ^a <: Int -> Int
-->{solve}
done!

^a, ^a <: Int -> Int, ^a <: Bot -> Int
-->{solve}
^a, Bot -> Int <: Int -> Int
-->
fail! (would suceed with:  ^a = Int -> Int   )

^a, ^a <: Top -> Int, ^a <: Int -> Int
-->{solve}
^a, Int -> Int <: Top -> Int
-->
fail!

With polarized substitution:

^a, Int -> Int <: ^a, ^a <: Bot -> Int
-->{solve}
^a, Int -> Int <: Bot -> Int
-->{success}



^a, ^a <: Int -> Int, ^a <: Bot -> Top
-->{}
^a, ^a <: Int -> Int
-->{solve}
done!




f :: Bot -> Int     <- not bottom-like or top-like
f x = x


-}
