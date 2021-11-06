{-# OPTIONS -XFlexibleContexts #-}

import Prelude hiding (flip)
import Data.List

import Debug.Trace
import Control.Monad.Writer

{- A revised ICFP algorithm with Top/Bot:

A,B := Int | A -> B | forall a. A | Top | Bot
T ::= . | T,a | T,^a | T |- A <: B

Algorithm:

(T, a)*                      = T*                                                     
(T, ^a)*                     = T*                                                     
(T |- Int <: Int)*           = T*                                                     
(T[a]  |- a <: a)*           = T*                                                     
(T[^a] |- ^a <: ^a)*         = T*
(T |- A <: Top)*             = T*
(T |- Bot <: A)*             = T*
(T,^a |- ^a <: Bot)*         = T*
(T,^a |- Top <: ^a)*         = T*
(T |- ^a <: Bot)*            = [[Bot/^a]] T           -- relies on order: basically the top work is not ^a
(T |- Top <: ^a)*            = [[Top/^a]] T           -- relies on order: basically the top work is not ^a
(T |- A -> B <: C -> D)*     = (T |- C <: A |- B <: D)*                                
(T |- A <: forall b . B)*    = (T,b |- A <: B)*                                         
(T |- forall a . B <: C)*    = (T,^a |- [^a/a] B <: C)*                               
(T |- ^a <: t)*              = ([t/^a]_{} T)* \/ (T |- ^a <: Bot)*                                           
(T |- t <: ^a)*              = ([t/^a]_{} T)* \/ (T |- Top <: ^a)*                                           
(T |- ^a <: A -> B)*         = ([^a1 -> ^a2/^a]_{^a1,^a2} T |- ^a1 -> ^a2 <: A -> B)* \/ (T |- ^a <: Bot )* 
       when not monotype (A->B)  
(T |- A -> B <: ^a)*         = ([^a1 -> ^a2/^a]_{^a1,^a2} T |- A -> B <: ^a1 -> ^a2)* \/ (T |- Top <: ^a)* 
       when not monotype (A->B)  

--------------
[A/^a]s_E T
--------------

Normal cases:

[A/^a]_E (T,^a)             = T,E                 ^a notin fv(A)
[A/^a]_E (T,^b)             = [A/^a]_E T,^b       ^b notin FV(A)
[A/^a]_E (T,^b)             = [A/^a]_{E,^b} T     ^b in FV(A)
[A/^a]_E (T |- B <: C)      = [A/^a]_E T |- [A/^a] B <: [A/^a] C

----------
[[t/^a]] T
----------
(Relying on pattern order here to simplify the logic a bit)

[[Top/^a]] (T, ^a, Top <: ^a) = T, ^a, Top <: ^a
[[Bot/^a]] (T, ^a, ^a <: Bot) = T, ^a, ^a <: Bot
[[Top/^a]] (T, ^a, ^a <: Bot) = Top <: Bot       -- failure
[[Bot/^a]] (T, ^a, Top <: ^a) = Top <: Bot       -- failure
[[Top/^a]] (T,^a)             = T,^a,Top <: ^a
[[Bot/^a]] (T,^a)             = T,^a,^a <: Bot
[[t/^a]]   (T,w)              = ([[t/^a]] T), w



Concerns:

The system is non-deterministic when the substituted monotype is ^a

Size Measures:

The size measures are a 2 element tuple where the measures have decreasing importance
as follows:

Measure 1 (always decreasing): number of existentials < splits * 2 + foralls + existentials in worklist

Measure 2 (size of worklist, decreases in the first 8 rules, only increases when the measure 1 decreases)       

-}

data Typ = TVar (Either Int Int) | TInt | TForall (Typ -> Typ) | TArrow Typ Typ | TTop | TBot

data Work = V (Either Int Int) | Sub Typ Typ deriving Eq

ppTyp :: Int -> Typ -> String
ppTyp n (TVar (Left i))  = show i
ppTyp n (TVar (Right i)) = "^" ++ show i
ppTyp n TInt             = "Int"
ppTyp n TTop             = "Top"
ppTyp n TBot             = "Bot"
ppTyp n (TArrow a b)     = "(" ++ ppTyp n a ++ ") -> " ++ ppTyp n b
ppTyp n (TForall f)      = "forall " ++ show n ++ ". " ++ ppTyp (n+1) (f (TVar (Left n)))  

eqTyp :: Int -> Typ -> Typ -> Bool
eqTyp n TInt TInt = True
eqTyp n TTop TTop = True
eqTyp n TBot TBot = True
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

subst :: Int -> Typ -> Typ -> Typ
subst i t TInt                    = TInt
subst i t TTop                    = TTop
subst i t TBot                    = TBot
subst i t (TVar v)                =
   case v of
     Right j | i == j             -> t
     _                            -> TVar v
subst i t (TArrow t1 t2)          = TArrow (subst i t t1) (subst i t t2)
subst i t (TForall g)             = TForall (\t1 -> subst i t (g t1))

fv :: Typ -> [Int]
fv (TVar (Right i)) = [i]
fv (TArrow t1 t2)   = fv t1 `union` fv t2
fv (TForall g)      = fv (g TInt)
fv _                = []

-- dealTB i TTop es = Sub TTop (TVar (Right i)) : V (Right i) : es
-- dealTB i TBot es = Sub (TVar (Right i)) TBot : V (Right i) : es
dealTB i _   es = es

substWL :: Int ->  Typ -> [Work] -> [Work] -> [Work]
substWL i t es (V (Right j) : ws)
   | i == j        = if (not (elem i (fv t))) then {-dealTB i t-} es ++ ws else error (show i ++ " in " ++ show t)
   | elem j (fv t) = substWL i t ((V . Right $ j) : es) ws
   | otherwise     = V (Right j) : substWL i t es ws
substWL i t es (Sub t1 t2 : ws) = Sub (subst i t t1) (subst i t t2) : substWL i t es ws

mono :: Typ -> Bool
mono (TForall g)  = False
mono (TArrow a b) = mono a && mono b
mono TTop         = False
mono TBot         = False
mono _            = True

printStep ws name = "   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ name ++ " \t\t\t Size: " ++ show (size ws) ++ "}\n"

evalSolve :: Int -> Int -> Typ -> [Work] -> [Work] -> Writer String Bool
evalSolve n i b sws ws = do t <- eval n sws
                            if t then return True
                                 else tell ("Failed: Trying ^" ++ show i ++ " = " ++ show b ++ "\n") >> eval n (substWL i b [] ws)

-- (substWL i a [] ws) (substWL i TBot [] ws)

{-

[[Top/^a]] (T, ^a, Top <: ^a) = T, ^a, Top <: ^a   -- ignore bound as it is already in the worklist
[[Bot/^a]] (T, ^a, ^a <: Bot) = T, ^a, ^a <: Bot   -- ignore bound as it is already in the worklist
[[Top/^a]] (T, ^a, ^a <: Bot) = Top <: Bot         -- failure
[[Bot/^a]] (T, ^a, Top <: ^a) = Top <: Bot         -- failure
[[Top/^a]] (T,^a)             = T,^a,Top <: ^a     -- insert bound earlier in the worklist
[[Bot/^a]] (T,^a)             = T,^a,^a <: Bot     -- insert bound earlier in the worklist
[[t/^a]]   (T,w)              = ([[t/^a]] T), w    -- recursive case

-}

solveBound :: Int -> Bool -> [Work] -> [Work]
solveBound i True o@(Sub TTop (TVar (Right j)) : V (Right k) : ws) | i == j && i == k = o
solveBound i False o@(Sub (TVar (Right j)) TBot : V (Right k) : ws) | i == j && i == k = o
solveBound i False o@(Sub TTop (TVar (Right j)) : V (Right k) : ws) | i == j && i == k = [Sub TTop TBot]
solveBound i True o@(Sub (TVar (Right j)) TBot : V (Right k) : ws) | i == j && i == k = [Sub TTop TBot]
solveBound i True o@(V (Right k) : ws) | i == k = Sub TTop (TVar (Right i)) : o
solveBound i False o@(V (Right k) : ws) | i == k = Sub (TVar (Right i)) TBot : o
solveBound i t (w : ws) = w : solveBound i t ws


eval :: Int -> [Work] -> Writer String Bool
eval n []                  = tell "Success!\n" >> return True
eval n (w : ws)            = let ps name = tell (printStep (w : ws) name) in 
  case w of
       (V i)                               -> ps "Garbage" >> eval n ws
       (Sub TInt TInt)                     -> ps "SInt" >> eval n ws
       (Sub (TVar i) (TVar j)) | i == j    -> ps "SVar" >> eval n ws
       (Sub a TTop)                        -> ps "STop" >> eval n ws
       (Sub TBot a)                        -> ps "SBot" >> eval n ws
       (Sub (TArrow a b) (TArrow c d))     -> ps "SArrow" >> eval n (Sub b d : Sub c a : ws)
       (Sub a (TForall g))                 -> ps "SForallR" >> eval (n+1) (Sub a (g (TVar (Left n))) : V (Left n) : ws)
       (Sub (TForall g) b)                 -> ps "SForallL" >> eval (n+1) (Sub (g (TVar (Right n))) b : V (Right n) : ws)
       (Sub (TVar (Right i)) TBot)         ->
         case ws of
           (V (Right j) : ws') | j == i    -> ps "SBotBase" >> eval n ws'
           _                               -> ps "MoveBot" >> eval n (solveBound i False ws)
       (Sub TTop (TVar (Right i)))         ->
         case ws of
           (V (Right j) : ws') | j == i    -> ps "STopBase" >> eval n ws'
           _                               -> ps "MoveTop" >> eval n (solveBound i True ws) 
       (Sub (TVar (Right i)) a) | mono a   -> ps "SolveL" >> evalSolve n i TBot (substWL i a [] ws) ws
       (Sub a (TVar (Right i))) | mono a   -> ps "SolveR" >> evalSolve n i TTop (substWL i a [] ws) ws 
       (Sub (TVar (Right i)) (TArrow a b)) -> ps "SplitL" >> evalSolve (n+2) i TBot (Sub a a1 : Sub a2 b : substWL i a1_a2 [V . Right $ n,V . Right $ n+1] ws) ws where
            a1 = TVar (Right n)
            a2 = TVar $ Right (n + 1)
            a1_a2 = TArrow a1 a2
       (Sub (TArrow a b) (TVar (Right i))) -> ps "SplitR" >> evalSolve (n+2) i TTop (Sub a1 a : Sub b a2 : substWL i a1_a2 [V. Right $ n,V . Right $ n+1] ws) ws where
            a1 = TVar (Right n)
            a2 = TVar $ Right (n + 1)
            a1_a2 = TArrow a1 a2
       _                                   -> ps "Failure" >> return False

chkOpen n = putStrLn . snd . runWriter . eval n

chk = chkOpen 0


t1 = TForall (\a -> TArrow a a)

t2 = TArrow t1 (TForall (\a -> TArrow a TTop))

t3 = TArrow TInt TInt

t5 = TForall (\t -> t)

t6 = TArrow TInt TTop
t7 = TArrow t6 t6

test1 = chk [Sub t3 t3]
test2 = chk [Sub t1 t3]
test3 = chk [Sub t5 t3] 
test4 = chk [Sub t5 t1]
test5 = chk [Sub t1 t6]
test6 = chk [Sub t6 t3]

test7 = chk [Sub t5 t7]

-- failing case 20200810
test8 = chk [Sub (TForall $ \a -> TArrow a a) (TArrow t5 (TArrow TBot TTop))]

test9 = chk [Sub (TForall $ \a -> (TArrow a (TArrow a TInt))) (TArrow t3 (TArrow (TArrow TBot TTop) TTop))]

-- Interesting example showing that in the presence of Top,
-- many examples can simply use Top for instantiation.
test10 = chk [Sub (TForall $ \a -> (TArrow a (TArrow a TInt))) (TArrow t3 (TArrow TInt TTop))]

tEx = TVar . Right

ex1 = tEx 1
ex2 = tEx 2

test11 = 
  chkOpen 4 [Sub ex1 (TArrow TInt ex2), Sub ex2 (TArrow TInt ex1), V (Right 2), V (Right 1)]

-- SIZES

-- number of splits, ws, size

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

jimmy = chkOpen 3 [
  Sub TInt TInt,
  Sub ex0 (TArrow TInt TInt),
  Sub (TArrow ex0 (TArrow ex0 $ TForall $ \a -> a)) ex1,
  V (Right 0),
  V (Right 1),
  V (Right 2)
  ]

---------------------------
-- Jimmy's looping programs
---------------------------

-- ^a |- ^a <: ^a |- Int <: ^a

loop1 = chkOpen 1 [Sub TInt ex0,Sub ex0 ex0, V (Right 0)]



-- [^a] [^b] [^c] ||- ^a -> ^a -> ^a <: ^a -> (^b -> ^b) -> ^c -> ^c

loop2 = chkOpen 3 [
  Sub (TArrow ex0 (TArrow ex0 ex0)) (TArrow ex0 (TArrow (TArrow ex1 ex1 ) (TArrow ex2 ex2))),
  V (Right 0),
  V (Right 1),
  V (Right 2)]

-- [^a] [^b] [^c] ||- ^a -> ^b -> ^a <: (^b -> ^b) -> ^c -> ^c -> ^c

loop3 = chkOpen 3 [
  Sub (TArrow ex0 (TArrow ex1 ex0)) (TArrow (TArrow ex1 ex1 ) (TArrow ex2 (TArrow ex2 ex2))),
  V (Right 0),
  V (Right 1),
  V (Right 2)]

-- [^a] [^b] [^c] ||- ^a -> Int -> ^a <: (^c -> ^c) -> ^b -> ^b -> ^b

loop4 = chkOpen 3 [
  Sub (TArrow ex0 (TArrow TInt ex0)) (TArrow (TArrow ex2 ex2 ) (TArrow ex1 (TArrow ex1 ex1))),
  V (Right 0),
  V (Right 1),
  V (Right 2)]

-------------------------
-- Jimmy's incompleteness
-------------------------

-- ^a, ^a <: Int -> Int, ^a <: Int -> Top

test12 = chkOpen 1 [Sub ex0 (TArrow TInt TTop), Sub ex0 (TArrow TInt TInt), V (Right 0)]

-- ^a, ^a <: Top -> Int, ^a <: Int -> Int

test13 = chkOpen 1 [Sub ex0 (TArrow TInt TInt), Sub ex0 (TArrow TTop TInt), V (Right 0)]

--

test14 = chkOpen 1 [Sub ex0 (TArrow TInt TTop), Sub ex0 (TArrow TInt TInt), Sub (TArrow TInt TInt) ex0, V (Right 0)]

test15 = chkOpen 3 [
  Sub ex0 (TArrow TInt ex1),
  Sub TTop ex1,
  Sub ex0 (TArrow TInt TInt),
  Sub (TArrow TInt TInt) ex0,
  V (Right 1),
  V (Right 0)]

test16 = chkOpen 3 [
  Sub ex0 ex1,
  Sub TTop ex1,
  Sub ex0 TInt,
  Sub TInt ex0,
  V (Right 0),
  V (Right 1)]

{-

[^0,^0 <: (Int) -> Int,^0 <: (Int) -> Top]
-->
[^0,^1, ^0 <: (Int) -> Int,^0 <: (Int) -> ^1]
-->
[^0,^1, Int -> ^1 <: (Int) -> Int]
-->
[^0,^1, Int <: Int, ^1 <: (Int)]
-->
[^0,^1, Int <: Int]
-->
[^0,^1]
-->
Success!

^a, ^b, ^c, ^a <: ^b -> ^c, ^c -> ^c <: ^c
-->
^a, ^b, ^c, Top <: ^c, ^a <: ^b -> ^c
--> 

T |- A -> B <: ^a = [^a/^a]_{^a, Top <: ^a} T  -- decreases size

-}

-- forall a . Int -> a <: Int -> Top



