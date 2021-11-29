import Prelude hiding (flip)
import Data.List

import Debug.Trace



data Typ = TVar (Either Int Int) | TInt | TBot | TTop | TForall (Typ -> Typ) | TArrow Typ Typ

data Work = V (Either Int Int) | Sub Typ Typ deriving Eq

ppTyp :: Int -> Typ -> String
ppTyp n (TVar (Left i))  = show i
ppTyp n (TVar (Right i)) = "^" ++ show i
ppTyp n TInt             = "Int"
ppTyp n TBot             = "Bot"
ppTyp n TTop             = "Top"
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

t1 = TForall (\a -> TArrow a a)

t2 = TArrow t1 (TForall (\a -> TArrow a TTop))

t3 = TArrow TInt TInt

data Mode = Pos | Neg | Equal deriving (Eq,Show)

instance Ord Mode where
  Pos <= Equal = True
  Neg <= Equal = True
  m1  <= m2    = m1 == m2

varId :: Either Int Int -> Int
varId (Left i) = i
varId (Right i) = i

flip :: Mode -> Mode
flip Pos   = Neg
flip Neg   = Pos
flip Equal = Equal

subst :: Either Int Int -> Mode -> Typ -> Typ -> Typ
subst i m t TInt                  = TInt
subst i m t TBot                  = TBot
subst i m t TTop                  = TTop
subst i m t (TVar v)
   | i == v  && (Pos <= m)        = t
   | otherwise                    = TVar v
subst i m t (TArrow t1 t2)        = TArrow (subst i (flip m) t t1) (subst i m t t2)
subst i m t (TForall g)           = TForall (\t1 -> subst i m t (g t1))

substWork :: Either Int Int -> Mode -> Typ -> Work -> Work
substWork i m t (V d)        = V d
substWork i m t (Sub t1 t2)  = Sub (subst i (flip m) t t1) (subst i m t t2)

substWorkList :: Either Int Int -> Mode -> Typ -> [Work] -> [Work]
substWorkList i m t = map (substWork i m t)

substWL :: Either Int Int -> Mode -> Typ -> [Work] -> [Work]
substWL i Equal t wl  = substWorkList i Equal t wl
-- substWL i m t wl      = [w1 | (w1, w2) <- zip (substWorkList i m t wl) wl, w1 /= w2 ] ++ wl   -- wrong; not producing new work
substWL i m t wl      = substWorkList i Equal t wl   -- wrong, for this system, but for size purposes only

hasFV :: Typ -> Either Int Int -> Bool
hasFV t i = t /= subst i Equal TInt t

processFun :: Either Int Int -> ([Work] -> [Work] -> [Work]) -> [Work] -> [Work]
processFun i f ws =
  let part = break (varId i ===) ws -- (... , ^a ...)
  in case part of
    (wL, vi:wR) -> f wL wR
    _           -> error "processFun: ^a not found"

process :: Either Int Int -> Mode -> Typ -> [Work] -> [Work]
process i m t =
  processFun i (\t1 t2 -> substWL i m t t1 ++ (V i) : t2)

isXBeforeY :: Int -> Int -> [Work] -> Bool
isXBeforeY _ _ [] = error "isXBeforeY: ^x nor ^y found in ws"
isXBeforeY x y (V (Right a) : ws) | a == x    = False
                                  | a == y    = True
isXBeforeY x y (_ : ws) = isXBeforeY x y ws

(===) :: Int -> Work -> Bool
(===) i (V (Right j)) = i == j
(===) i _             = False

step :: Int -> [Work] -> (Int, Int, [Work], String)
step n (V i : ws)            = (n, 1, ws, "Garbage Collection")     --    T, a --> T   /\  T, ^a --> T
step n (Sub a TTop : ws)     = (n, 1, ws, "STop")                   --    T ||- A <: Top      --> T
step n (Sub TBot a : ws)     = (n, 1, ws, "SBot")                   --    T ||- Bot <: A      --> T
step n (Sub TInt TInt : ws)  = (n, 1, ws, "SInt")                   --    T ||- Int <: Int    --> T
step n (Sub (TVar i) (TVar j) : ws)                             -- TODO: need to check if defined
                  | i == j   = (n, 1, ws, "SUVar")                  --    T ||- a <: a      --> T /\ T ||- ^a <: ^a      --> T 
step n (Sub (TArrow a b) (TArrow c d) : ws) =
                  (n, 3, Sub b d : Sub c a : ws, "SArrow")         --    T ||- a -> b <: c -> d --> T ||- c <: a |- b d
step n (Sub a (TForall g) : ws) =                               --    T ||- a <: forall b . c --> T,a ||- a <: c 
  (n+1, 2, Sub a (g (TVar (Left n))) : V (Left n) : ws, "SForallR")
step n (Sub (TForall g) b : ws) =                               --    T ||- forall a . b <: c --> T,^a ||- [a/^a] b <: c 
  (n+1, 2, Sub (g (TVar (Right n))) b : V (Right n) : ws, "SForallL") 
step n (Sub TTop (TVar v@(Right i)) : ws)     =                   --    T1,^b,T2     ||- Top <: ^b    --> T1, [^b/Top] T2
  (n, 1, process v Equal TTop ws, "STopSolve")
step n (Sub (TVar v@(Right i)) TBot : ws)     =                   --    T1,^b,T2     ||- ^b <: Bot    --> T1, [^b/Bot] T2
  (n, 1, process v Equal TBot ws, "SBotSolve")
step n (Sub (TVar (Left j)) (TVar v@(Right i)) : ws) =            --    T1[a],^b,T2  ||- a <: ^b      --> T1[a], ^b, [^b/a]- T2
  (n, 1, process v Neg (TVar (Left j)) ws, "SUniSolveL")           --    TODO: check if "a" is in t1
step n (Sub (TVar v@(Right i)) (TVar (Left j))  : ws) =           --    T1[a],^b,T2  ||- ^b <: a      --> T1[a], ^b, [^b/a]+ T2
  (n, 1, process v Pos (TVar (Left j)) ws, "SUniSolveR")           --    TODO: check if "a" is in t1
step n (Sub TInt (TVar v@(Right i)) : ws)     =                   --    T1,^b,T2     ||- TInt <: ^b    --> T1, [^b/Int]- T2
  (n, 1, process v Neg TInt ws, "SIntSolveL")
step n (Sub (TVar v@(Right i)) TInt : ws)     =                   --    T1,^b,T2     ||- ^b <: TInt    --> T1, [^b/Int]+ T2
  (n, 1, process v Pos TInt ws, "SIntSolveR")

--    T1,^a,T2     ||- ^a <: A -> B --> T1,^a1,^a2,^a [^a/^a1->^a2]+ T2 ||- ^a1 -> ^a2 <: A -> B     if not (^a in fv(A -> B))   
step n (Sub (TVar v@(Right i)) (TArrow a b) : ws) =
  if (TArrow a b) `hasFV` v then
    error "^a <: A -> B case: ^a in FV(A -> B)"
  else
    (n + 2, 5, ws', "SplitL")
  where
    a1 = Right n
    a2 = Right (n + 1)
    a1_a2 = TArrow (TVar a1) (TVar a2)
    ws' = processFun v (\t1 t2 -> Sub a1_a2 (TArrow a b) : substWL v Pos a1_a2 t1 ++ [V (Right i), V a1, V a2] ++ t2) ws

--    T1,^a,T2     ||- A -> B <: ^a --> T1,^a1,^a2,^a [^a/^a1->^a2]- T2 ||- A -> B <: ^a1 -> ^a2     if not (^a in fv(A -> B))
step n (Sub (TArrow a b) (TVar v@(Right i)) : ws) =
  if (TArrow a b) `hasFV` v then
    error "^a <: A -> B case: ^a in FV(A -> B)"
  else
    (n + 2, 5, ws', "SplitR")
  where
    a1 = Right n
    a2 = Right (n + 1)
    a1_a2 = TArrow (TVar a1) (TVar a2)
    ws' = processFun v (\t1 t2 -> Sub (TArrow a b) a1_a2 : substWL v Neg (TArrow (TVar a1) (TVar a2)) t1 ++ [V (Right i), V a1, V a2] ++ t2) ws

step n (Sub (TVar v@(Right i)) (TVar u@(Right j)) : ws)
  | isXBeforeY i j ws =                                         -- T1[^a],^b,T2 ||- ^a <: ^b     --> T1[^a], ^b, [^b/^a]- T2
    (n, 1, process v Pos (TVar (Right j)) ws, "SExSolveL")
  | otherwise         =                                         -- T1[^a],^b,T2 ||- ^b <: ^a     --> T1[^a], ^b, [^b/^a]+ T2
    (n, 1, process u Pos (TVar (Right i)) ws, "SExSolveR")


-- step n (Sub (TVar (Right i)) (TArrow a b) : ws)  =
--   let (x:t2,t1) = span (i ===) (reverse ws)
--       s1 = Sub (TArrow (TVar (Right n)) (TVar (Right (n+1)))) (TArrow a b)
--   in (n, s1 : substWL i Neg (TArrow (TVar (Right n)) (TVar (Right (n+1)))) t1 ++ x : [V (Right (n+1)), V (Right n)] ++ t2, "SplitL")

check :: Int -> [Work] -> (String,Int)
check n [] = ("Success!",0)
check n ws =
  let (m,i,ws',s1) = step n ws
      (s2,acc)     = check m ws'
      nacc         = i + acc
  in ("   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ " \t\t\t Size: " ++ show (size n 1 ws) ++ " }\n" ++ s2, nacc)

chk = putStrLn . fst . check 0

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

tEx = TVar . Right

ex1 = tEx 1
ex2 = tEx 2

test9 = putStrLn . fst $
  check 4 [Sub ex1 (TArrow TInt ex2), Sub ex2 (TArrow TInt ex1), V (Right 2), V (Right 1)]


-- SIZES

-- number of splits, ws, size

size :: Int -> Int -> [Work] -> Int
size n k []              = 0
size n k (V i : ws)      = 1 + size n k ws
size n k (Sub a b : ws)  =
  let (s,k',m) = sizeSub n k a b 
  in  s + size m k' ws 

sizeSub :: Int -> Int -> Typ -> Typ -> (Int,Int,Int)
-- 1 unit of work +       
-- number of splits *
-- (3 entries in env (2 new elements for existential + 1 more element from split) + arrow break + split weight propagation) *
-- k (the weight for each var) 
{-

Detailed explanation:

- There's 1 unit of work for processing a split rule

- Then there are a number of things that depend on the number
  of splits that we have:

  1) +2: each split adds 2 entries on the environment
  2) +1: each split breaks an arrow type (which adds one more entry)
  3) +k: each split adds an extra existential variable, which has size k
     Here: size k = number of splits in the entries that appear earlier + 1
  4) +1: however one of the existential variables will be used deeper in the worklist and will carry additional weight.

     For example:

     [^0, ^0 <: Int -> Int -> Int]

     splits and then breaks into:

     [^1,^2,^0, Int <: ^1, ^2 <: Int -> Int]

     the weight of ^2 will be 1, but the weight of ^1 should be higher because, in a slightly different worklist:

     [^1,^2,^0, Int <: ^1, ^1 <: Int -> Int]

     the work "^1 <: Int -> Int" would lead to a split, and the earlier ^1 would become an arrow of two existentials:

     [^3,^4,^1,^2,^0, Int <: ^3 -> ^4, ^3 -> ^4 <: Int -> Int]

     Therefore the weight with existentials that appear earlier in new work generated by a split needs
     to give extra weight to those variables. This is why we have the extra +1.


  Thus we have: the number of splits * (k + 5)

   [^0,forall 0. 0 <: ^0,^0 <: (Bot) -> Top]   
-->{ Rule: SplitL 			 Size: 12 }  -- (1 + 6) + (2+2) + 1
   [^2,^1,^0,forall 0. 0 <: (^1) -> ^2,(^1) -> ^2 <: (Bot) -> Top]
-->{ Rule: SArrow 			 Size: 15 }  -- (1 + 1 + 1) + (2 + 1 + 6) + 3


-}

sizeSub n k (TVar (Right i)) t@(TArrow _ _)   =
  (1 + splits t * (k+5), splits t + k, n)   
sizeSub n k t@(TArrow _ _) (TVar (Right i))   = (1 + splits t * (k+5), splits t + k, n)
sizeSub n k (TArrow a b) (TArrow c d)         = 
  let (s1,k',n')  = sizeSub n k b d                        
      (s2,k'',n'') = sizeSub n' k' c a
  in (1 + s1 + s2,k'',n'')
sizeSub n k a (TForall g)                       =
  let (s,k',n') = sizeSub (n+1) k a (g (TVar (Left n)))
  in (2 + s,k',n')
sizeSub n k (TForall g) a                       =
  let (s,k',n') = sizeSub n k (g (TVar (Right 10))) a
  in (2 + s,k',n')
sizeSub n k (TVar (Right i)) a                = (k, k, n)    -- missing new work
sizeSub n k a (TVar (Right i))                = (k, k, n)
sizeSub n k a b                               = (1, k, n)


splits (TArrow a b) = 1 + splits a + splits b
splits (TForall g)  = splits (g TTop)
splits _            = 0

jimmy = putStrLn $ fst $ check 3 [
  Sub (TVar (Right 0)) (TArrow TInt TInt),
  Sub (TArrow (TVar (Right 0)) (TVar (Right 0))) (TVar (Right 0)),
  V (Right 0),
  V (Right 1),
  V (Right 2)
  ]

{-

  [^0,^0 <: ((Int) -> Top) -> (Int) -> Top]                  -- 1 + (1 + 3 * 5) = 17
-->{ Rule: SplitL 			 Size: 17 }
   [^2,^1,^0,(^1) -> ^2 <: ((Int) -> Top) -> (Int) -> Top]   -- 3 + 1
-->{ Rule: SArrow 			 Size: 17 }          


size :: Int -> [Work] -> Int
size n []              = 0
size n (V i : ws)      = 1 + size n ws
size n (Sub a b : ws)  =
  let s = size n ws
  in sizeSub n s a b -- + s

-- #ex, size(ws), A, B
sizeSub :: Int -> Int -> Typ -> Typ -> Int
sizeSub n acc (TVar (Right i)) (TArrow a b)     =
  let prev = sizeSub (n+2) (2*(sizeTyp b)*acc + acc) a (TVar (Right n))   -- adds at most 2*(sizeTyp b) variables to environment
  in sizeSub (n+2) (3+prev) (TVar (Right (n+1))) b                    -- one more element; one arrow split; one split
sizeSub n acc (TArrow a b) (TVar (Right i))     =
  let prev = sizeSub (n+2) (2*(sizeTyp b)*acc + acc) (TVar (Right n)) a   -- adds at most 2*(sizeTyp b) variables to environment
  in sizeSub (n+2) (3+prev) b (TVar (Right (n+1)))                    -- one more element; one arrow split; one split
sizeSub n acc (TArrow a b) (TArrow c d)           = 
  let prev = sizeSub n acc c a                        
  in sizeSub n (2 + prev) b d                                         -- one more element to the list + one arrow split
sizeSub n acc a (TForall g)                       =
  sizeSub (n+1) (2 + acc) a (g (TVar (Left n)))                       -- one more element + one forall elim
sizeSub n acc (TForall g) a                       =
  sizeSub (n+1) (2 + acc) (g (TVar (Right n))) a                      -- one more element + one forall elim
sizeSub n acc (TVar (Right i)) a                  = 1 + 2 * acc   -- worst case the type variable solving should cost < 2 * acc
sizeSub n acc a (TVar (Right i))                  = 1 + 2 * acc
sizeSub n acc a b                                 = 1 + acc   -- one unit of work + all work so far

sizeTyp (TArrow a b) = sizeTyp a + sizeTyp b
sizeTyp (TForall g)  = sizeTyp (g TTop)
sizeTyp _            = 1
-}
{-

   [^2,^1,^0,(Int) -> Top <: ^1,^2 <: (Int) -> Top]
-->{ Rule: SplitL 			 Size: 133 }
   [^4,^3,^2,^1,^0,(Int) -> Top <: ^1,(^3) -> ^4 <: (Int) -> Top]
-->{ Rule: SArrow 			 Size: 155 }

What's the problem above? Well, the problem is that splitting:

^2 <: (Int) -> Top

will add 2 elements to the list. In turn this will affect computing the size of:

[^2,^1,^0,(Int) -> Top <: ^1]

since the size of the above is smaller than:

[^4,^3,^2,^1,^0,(Int) -> Top <: ^1]


  [^2,^1,^0,(Int) -> Top <: ^1,^2 <: (Int) -> Top]
-->{ Rule: SplitL 			 Size: 133 }
   [^4,^3,^2,^1,^0,(Int) -> Top <: ^1,(^3) -> ^4 <: (Int) -> Top]
-->{ Rule: SArrow 			 Size: 155 }

-}

{-
sizeSub :: Int -> Int -> Int -> Typ -> Typ -> Int
sizeSub n factor br (TVar (Right i)) a@(TArrow _ _)     =
  1 + sizeSub (n+2) (3 + 2*factor) br a (TArrow (TVar (Right n)) (TVar (Right (n+1))))
sizeSub n factor br a@(TArrow _ _) (TVar (Right i))     =
  1 + sizeSub (n+2) (3 + 2*factor) br (TArrow (TVar (Right n)) (TVar (Right (n+1)))) a 
sizeSub n factor br (TArrow a b) (TArrow c d)           =
  let prev = sizeSub n factor br c a
  in 1 + prev + sizeSub n (prev+factor) (1+br) b d
sizeSub n factor br a (TForall g)                       =
  2 + sizeSub (n+1) br (1+factor) a (g (TVar (Left n)))
sizeSub n factor br (TForall g) a                       =
  2 + sizeSub (n+1) br (1+factor) (g (TVar (Right n))) a
sizeSub n factor br (TVar (Right i)) a                  = br + factor 
sizeSub n factor br a (TVar (Right i))                  = br + factor 
sizeSub n factor br a b                                 = br
-}

{-
size :: Int -> [Work] -> Int
size n []              = 0
size n (V i : ws)      = 1 + size n ws
size n (Sub a b : ws)  =
  let factor = size n ws
  in sizeSub n factor 1 a b + factor 

sizeSub :: Int -> Int -> Int -> Typ -> Typ -> Int
sizeSub n factor br (TVar (Right i)) a@(TArrow _ _)     = br + 3 * factor * sizeTyp factor a
sizeSub n factor br a@(TArrow _ _) (TVar (Right i))     = br + 3 * sizeTyp factor a
sizeSub n factor br (TVar (Right i)) a                  = br + factor * sizeTyp factor a
sizeSub n factor br a (TVar (Right i))                  = br + factor * sizeTyp factor a
sizeSub n factor br (TArrow a b) (TArrow c d)           = 1 + sizeSub n factor (br+1) c a + sizeSub n factor (br+1) b d
sizeSub n factor br a (TForall g)                       = 2 + sizeSub (n+1) br factor a (g (TVar (Left n)))
sizeSub n factor br (TForall g) a                       = 2 + sizeSub (n+1) br (1+factor) (g (TVar (Right n))) a
sizeSub n factor br a b                                 = br
-- sizeSub n a TTop                        = 1
-- sizeSub n TBot a                        = 1
-- sizeSub n TInt TInt                     = 1


sizeTyp factor (TArrow a b)      = sizeTyp factor a + sizeTyp factor b
sizeTyp factor (TForall g)       = sizeTyp factor (g TTop)
sizeTyp factor (TVar (Right i))  = factor
sizeTyp factor _                 = 1
-}

{-
fev :: Typ -> [Int]
fev (TArrow a b) = fev a `union` fev b
fev (TForall g)  = fev (g TTop)
fev _            = []

size :: Int -> [Work] -> Int
size n []              = 0
size n (V i : ws)      = 1 + size n ws
size n (Sub a b : ws)  =
  let factor = size n ws
  in sizeSub n a b + factor + length (fev a `union` fev b) * factor

sizeSub :: Int -> Typ -> Typ -> Int
sizeSub n (TVar (Right i)) a@(TArrow _ _)            = 1 + 3 * sizeTyp a
sizeSub n a@(TArrow _ _) (TVar (Right i))            = 1 + 3 * sizeTyp a
sizeSub n (TVar (Right i)) a                         = sizeTyp a
sizeSub n a (TVar (Right i))                         = sizeTyp a
sizeSub n (TArrow a b) (TArrow c d)                  = 1 + sizeSub n c a + sizeSub n b d
sizeSub n a (TForall g)                              = 2 + sizeSub (n+1) a (g (TVar (Left n)))
sizeSub n (TForall g) a                              = 2 + sizeSub (n+1) (g (TVar (Right n))) a
sizeSub n a b                                        = 1
-- sizeSub n a TTop                        = 1
-- sizeSub n TBot a                        = 1
-- sizeSub n TInt TInt                     = 1


sizeTyp (TArrow a b) = sizeTyp a + sizeTyp b
sizeTyp (TForall g)  = sizeTyp (g TTop)
sizeTyp _            = 1
-}

{- Missing:

DONE: T1[^a],^b,T2 ||- ^a <: ^b     --> T1[^a], ^b, [^b/^a]- T2
DONE: T1[^a],^b,T2 ||- ^b <: ^a     --> T1[^a], ^b, [^b/^a]+ T2

DONE & fixed: T1,^a,T2     ||- A -> B <: ^a --> T1,^a1,^a2,^a [^a/^a1->^a2]+ T2 ||- A -> B <: ^a1 -> ^a2     if not (^a in fv(A -> B))

propagate number of splits, size of an existential bounded by the number of splits?

-}

-- step n (Sub (TVar (Left i)) (TVar (Right j)) : ws) =    --    T1[a],^b,T2  ||- a <: ^b  --> T1[a], ^b, [^b/a]- T2

{-

Syntax:

A,B := Top | Bot | Int | A -> B | forall a. A 
T ::= . | T,a | T,^a | T ||- A <: B

Algorithm:

Size of T decreases:

T, a                          --> T        
T, ^a                         --> T
T ||- A <: Top                --> T
T ||- Bot <: A                --> T
T ||- Int <: Int              --> T
T[a]  ||- a <: a              --> T
T[^a] ||- ^a <: ^a            --> T

size (T,K) = 1 + size(T)
size (T,U) = 1 + 2*constraints(T) + size(T)
size (T,S) = 1 + splits(A->B) + size(T)

Size of T decreases or there new work
with some solved variables.

T1,^b,T2     ||- Top <: ^b    --> T1, [^b/Top] T2
T1,^b,T2     ||- ^b <: Bot    --> T1, [^b/Bot] T2
T1[a],^b,T2  ||- a <: ^b      --> T1[a], ^b, [^b/a]- T2
T1[a],^b,T2  ||- ^b <: a      --> T1[a], ^b, [^b/a]+ T2
T1,^b,T2     ||- Int <: ^b    --> T1, ^b, [^b/Int]- T2
T1,^b,T2     ||- ^b <: Int    --> T1, ^b, [^b/Int]+ T2
T1[^a],^b,T2 ||- ^a <: ^b     --> T1[^a], ^b, [^b/^a]- T2
T1[^a],^b,T2 ||- ^b <: ^a     --> T1[^a], ^b, [^b/^a]+ T2

Size of types decreases:

T ||- A -> B <: C -> D        --> T ||- C <: A |- B <: D
T ||- A <: forall b . B       --> T,b ||- A <: C
T ||- forall a . B <: C       --> T,^a ||- [a/^a] B <: C

The difference of the sizes of types decreases,
but the size of T2 increases by the number of
positive/negative occurrences of ^a

T1,^a,T2     ||- ^a <: A -> B --> T1,^a1,^a2,^a [^a/^a1->^a2]- T2 ||- ^a1 -> ^a2 <: A -> B     if not (^a in fv(A -> B))   
T1,^a,T2     ||- A -> B <: ^a --> T1,^a1,^a2,^a [^a/^a1->^a2]+ T2 ||- A -> B <: ^a1 -> ^a2     if not (^a in fv(A -> B))



Effects of splits:

- Splits will increase the size of the preceeding list because
  they will add new variables to the environment;

- Splits will substitute an existencial by an arrow of 2 existentials
  in the preceedig list

- 


size(T) : Int
size(.)               = 0
size(T,a)             = 1 + size(T)
size(T,^a)            = 1 + size(T)
size(T, A <: B)       = size(A,B) + size(T) + (#(fev(A) `union` fev(B))) * size(T) 


size(A,B) : Int
size(^a,B)             = size(B)
size(A,^b)             = size(A)
size(Int,Int)          = 1
size(A,Top)            = 1
size(Bot,A)            = 1
size(A -> B), C -> D)  =


size(T) : Int
size(.)               = 0
size(T,a)             = 1 + size(T)
size(T,^a)            = 1 + size(T)
size(T ||- A <: Top)  = 1 + size(T)
size(T ||- Bot <: A)  = 1 + size(T)
size(T ||- a <: a)    = 1 + size(T)
size(T ||- ^a <: ^b)  = 1 + size(T)
size(T ||- Int <: ^b) = 1 + size(T)
size(T ||- ^b <: Int) = 1 + size(T)
size(T ||- a <: ^b)   = 1 + size(T)
size(T ||- ^b <: a)   = 1 + size(T)
size(T ||- A -> B <: C -> D) = size(A) + size(B) + size(C) + size(D) + size(T)   -- cannot be too big this size
size(T ||- ^a <: A -> B) = occurrences(^a,T) + size(A) + size(B) + size(T)


size (T ||- Int <: Int) = 1
size (T ||- ^a  <: Int) = occurrences(^a,T) * length(T)

Example 1)

forall a . a -> a <: Int -> Top
-->
^a ||- ^a -> ^a <: Int -> Top
-->
^a ||- Int <: ^a ||- ^a <: Top
-->
^a ||- Int <: Top
-->
^a
-->
.

Example 2)

forall a . a -> a <: Top -> Int
-->
^a ||- ^a -> ^a <: Top -> Int
-->
^a ||- Top <: ^a ||- ^a <: Int
-->
^a ||- Top <: Int
-->
fail!

Example 3)
^b, ^a ||- ^a <: ^b ||- ^b <: ^a
-->
^b, ^a ||- ^b <: ^b
-->
^b, ^a
-->
^b
-->
.

Example 4)

^a, ^b, ^a <: 1 -> ^b, ^b <: 1 -> ^a
--->
^a, ^b1,^b2, ^a <: 1 -> ^b1 -> ^b2, ^b1 -> ^b2 <: 1 -> ^a
--->
^a, ^b1,^b2, ^a <: 1 -> ^b1 -> ^b2, 1 <: ^b1 , ^b2 <: ^a
--->
^a, ^b1,^b2, ^a <: 1 -> ^b1 -> ^a, 1 <: ^b1 
--->
^a, ^b1,^b2, ^a <: 1 -> 1 -> ^a
--->
fail!

-}


{- Use delayed substitutions?

    ^a, ^a <: Int, Top <: ^a, Int <: ^a
--> ^a, ([^a |-> Int]+ ^a) <: Int, Top <: ^a
--> ^a, ([^a |-> Top]+ ^a) <: Int
--> ^a, Top <: Int
--> fail

    ^a, ^a <: Int, Top <: ^a, Int <: ^a
--> ^a, ([^a |-> Int]+ ^a) <: Int, Top <: ^a
--> ^a, ([^a |-> Top]+ ^a) <: Int
--> ^a, Top <: Int
--> fail

-}

{-

Revisiting the ICFP Algorithm:

A,B := Int | A -> B | forall a. A 
T ::= . | T,a | T,^a | T ||- A <: B

Algorithm:

T, a                          --> T        
T, ^a                         --> T
T ||- Int <: Int              --> T
T[a]  ||- a <: a              --> T
T[^a] ||- ^a <: ^a            --> T
T ||- A -> B <: C -> D        --> T ||- C <: A |- B <: D
T ||- A <: forall b . B       --> T,b ||- A <: C
T ||- forall a . B <: C       --> T,^a ||- [^a/a] B <: C
T ||- ^a <: A                 --> [A/^a]+ T    when A+  and ^a notin fv(A) 
T ||- A <: ^a                 --> [A/^a]- T    when A-  and ^a notin fv(A)


A+ no positively bounded variables are used
A- no negatively bounded variables are used

[A/^a]s T = . |- [A/^a]s T

As = . |-s A

-------
E |-s A
-------

E |-s Int

X+ in E 
-------
E |-+ X

E |-(flip s) A    E |-s B
-------------------------
E |-s A -> B

E,Xs |-s A
------------------
E |-s forall X . A

--------------
E |- [A/^a]s T
--------------

E |- [A/^a]s .                  = .
E |- [A/^a]s (T,^a)             = T,E,^a
E |- [A/^a]s (T,^b)             = (E |- [A/^a]s T),^b       ^b notin FV(A)
E |- [A/^a]s (T,^b)             = E,^b |- [A/^a]s T         ^b in FV(A)
E |- [A/^a]s (T ||- B <: C)     = (E |- [A/^a]s T) ||- [A/^a](flip s) B <: [A/^a]s C

Concerns:

- Do I need to take special care with:

T ||- ^a <: ^b

The order of the variables is important to determine which substitution to perform.

The two last rules are non-deterministic in this case

Int -> Char <: ^a, Char -> Char <: ^a, ^a <: (forall a . a) -> Char 

 -}


{-

Revisiting the ICFP Algorithm:

A,B := Int | A -> B | forall a. A 
T ::= . | T,a | T,^a | T ||- A <: B

Algorithm:

T, a                          --> T        
T, ^a                         --> T
T ||- Int <: Int              --> T
T[a]  ||- a <: a              --> T
T[^a] ||- ^a <: ^a            --> T
T ||- A -> B <: C -> D        --> T ||- C <: A |- B <: D
T ||- A <: forall b . B       --> T,b ||- A <: C
T ||- forall a . B <: C       --> T,^a ||- [^a/a] B <: C
T ||- ^a <: t                 --> [t/^a]_{} T    
T ||- t <: ^a                 --> [t/^a]_{} T    
T ||- ^a <: A -> B            --> [^a1 -> ^a2/^a]_{^a1,^a2} T ||- ^a1 -> ^a2 <: A -> B
       when not monotype (A->B)  
T ||- A -> B <: ^a            --> [^a1 -> ^a2/^a]_{^a1,^a2} T ||- A -> B <: ^a1 -> ^a2
       when not monotype (A->B)  

--------------
[A/^a]_E T
--------------

[A/^a]_E (T,^a)             = T,E                 ^a notin fv(A)
[A/^a]_E (T,^b)             = [A/^a]_E T,^b       ^b notin FV(A)
[A/^a]_E (T,^b)             = [A/^a]_{E,^b} T     ^b in FV(A)
[A/^a]_E (T ||- B <: C)     = [A/^a]_E T ||- [A/^a] B <: [A/^a] C

Concerns:

The system is non-deterministic when the substituted monotype is ^a

 -}
