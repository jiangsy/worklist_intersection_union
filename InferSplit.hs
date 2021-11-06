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


