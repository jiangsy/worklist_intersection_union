import Data.Char
import Data.List
import Debug.Trace

data Typ = TTop | TBot | TInt | Fun Typ Typ | Var String | Nominal String deriving (Eq)

data Work = Exists Typ String Typ | Sub Typ Typ

type WorkList = [Work]

type NominalEnv = [(String, Maybe String)]

instance Show Typ where
  show TInt = "I"
  show TTop = "T"
  show TBot = "B"
  show (Fun a b) = "(" ++ show a ++ ") -> " ++ show b
  show (Var s) = "^" ++ s
  show (Nominal s) = s

showWork (Sub t1 t2) = show t1 ++ " <: " ++ show t2
showWork (Exists t1 s t2) = show t1 ++ " <: ^" ++ s ++ " <: " ++ show t2

instance {-# OVERLAPPING #-} Show WorkList where
  show [] = "."
  show [x] = showWork x
  show (x : xs) = show xs ++ ", " ++ showWork x

subst :: NominalEnv -> Int -> String -> Typ -> Bool -> WorkList -> Maybe WorkList
subst e f i t b o@(Sub t1 t2 : ws) = do
  ws' <- subst e f i t b ws
  return (Sub t1 t2 : ws')
subst e f i (Var j) b (Exists t1 s t2 : ws)
  | j == s = subst e f j (Var i) (not b) (Exists t1 s t2 : ws) -- j must be different from i
subst e f i t b (Exists t1 s t2 : ws)
  | i == s && b = do
      (t2', ws', ws'') <- glb e f t t2
      return (Exists t1 s t2' : (ws' ++ ws ++ ws''))
  | i == s && (not b) = do
      (t1', ws', ws'') <- lub e f t t1
      return (Exists t1' s t2 : (ws' ++ ws ++ ws''))
  | otherwise -- not fully correct as I ignore dependencies (but we know how to deal with this)
    =
      do
        ws' <- subst e f i t b ws
        return (Exists t1 s t2 : ws')

lub :: NominalEnv -> Int -> Typ -> Typ -> Maybe (Typ, WorkList, WorkList)
lub e _ TBot t = Just (t, [], [])
lub e _ t TBot = Just (t, [], [])
lub e _ TInt TInt = Just (TInt, [], [])
lub e _ (Nominal n1) (Nominal n2)
  | n1 == n2 || subN n1 n2 e = Just (Nominal n2, [], [])
  | subN n2 n1 e = Just (Nominal n1, [], [])
lub e f (Fun a b) (Fun c d) =
  do
    (t1, ws1, ws3) <- glb e f a c
    (t2, ws2, ws4) <- lub e (f + (length ws1 `div` 3)) b d -- Another hack for not dealing with freshness properly
    return (Fun t1 t2, ws1 ++ ws2, ws3 ++ ws4)
lub e f (Var i) t = let fr = show f in Just (Var fr, [Sub (Var i) (Var fr), Sub t (Var fr)], [Exists TBot fr TTop])
lub e f t (Var i) = let fr = show f in Just (Var fr, [Sub (Var i) (Var fr), Sub t (Var fr)], [Exists TBot fr TTop])
lub e _ _ _ = Nothing

glb :: NominalEnv -> Int -> Typ -> Typ -> Maybe (Typ, WorkList, WorkList)
glb e _ TTop t = Just (t, [], [])
glb e _ t TTop = Just (t, [], [])
glb e _ TInt TInt = Just (TInt, [], [])
glb e _ (Nominal n1) (Nominal n2)
  | n1 == n2 || subN n1 n2 e = Just (Nominal n1, [], [])
  | subN n2 n1 e = Just (Nominal n2, [], [])
glb e f (Fun a b) (Fun c d) =
  do
    (t1, ws1, ws3) <- lub e f a c
    (t2, ws2, ws4) <- glb e (f + (length ws1 `div` 3)) b d -- freshness hack
    return (Fun t1 t2, ws1 ++ ws2, ws3 ++ ws4)
glb e f (Var i) t = let fr = show f in Just (Var fr, [Sub (Var fr) (Var i), Sub (Var fr) t], [Exists TBot fr TTop])
glb e f t (Var i) = let fr = show f in Just (Var fr, [Sub (Var fr) (Var i), Sub (Var fr) t], [Exists TBot fr TTop])
glb e _ _ _ = Nothing

-- I know that the two nominal types are different

subN :: String -> String -> NominalEnv -> Bool
subN n1 n2 [] = False
subN n1 n2 ((n3, Nothing) : es)
  | n1 /= n3 && n2 /= n3 = subN n1 n2 es
  | otherwise = False
subN n1 n2 ((n3, Just n4) : es)
  | n1 == n3 && n2 == n4 = True
  | otherwise = subN (if n1 == n3 then n4 else n1) n2 es

-- I will need this, if I use Top and Bot in places other than the bound
mono :: Typ -> Bool
mono TTop = False
mono TBot = False
mono (Fun a b) = mono a && mono b
mono _ = True

-- run = maybe False id

solvable' e f = maybe False (solvable e f)

solvable :: NominalEnv -> Int -> WorkList -> Bool
solvable _ _ [] = True
-- Subtyping
solvable e f o@(Sub a TTop : ws) = trace (show o) $ solvable e f ws
solvable e f o@(Sub TBot a : ws) = trace (show o) $ solvable e f ws
solvable e f o@(Sub TInt TInt : ws) = trace (show o) $ solvable e f ws
solvable e f o@(Sub (Fun t1 t2) (Fun t3 t4) : ws) = trace (show o) $ solvable e f (Sub t3 t1 : Sub t2 t4 : ws)
-- cases for non-mono are missing
-- Note that, in the following I use a hack because I do not implement freshness properly (it would require a state monad)
solvable e f o@(Sub (Var i) t1 : ws) | mono t1 = trace (show o) $ solvable' e (5 + f) (subst e f i t1 True ws)
solvable e f o@(Sub t1 (Var i) : ws) | mono t1 = trace (show o) $ solvable' e (5 + f) (subst e f i t1 False ws)
solvable e f o@(Sub (Nominal n1) (Nominal n2) : ws)
  | n1 == n2 || subN n1 n2 e = trace (show o) $ solvable e f ws
  | otherwise = trace (show o) $ False
-- Existentials
solvable e f o@(Exists t1 s t2 : ws) = trace (show o) $ solvable e f (Sub t1 t2 : ws)
solvable e f o = trace (show o) $ False

nomEnv = [("Grad", Just "Student"), ("Student", Just "Person"), ("Person", Nothing), ("Oak", Just "Tree"), ("Tree", Just "Plant"), ("Plant", Nothing)]

solve = solvable nomEnv 0

w1 = [Sub TInt TInt, Exists TBot "a" TTop]

w2 = [Sub (Var "a") TInt, Exists TBot "a" TTop]

w3 = [Sub (Var "a") (Fun TInt TInt), Sub (Var "a") TInt, Exists TBot "a" TTop]

w4 = [Sub (Fun (Var "a") (Var "a")) (Fun (Fun TInt TInt) (Fun TInt TInt)), Sub (Fun (Var "a") (Var "a")) (Fun TInt TInt), Exists TBot "a" TTop]

w5 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Student")), Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Person")), Exists TBot "a" TTop]

w6 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Student")), Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Student") (Nominal "Person")), Exists TBot "a" TTop]

w7 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Person")), Sub (Fun (Nominal "Student") (Nominal "Person")) (Fun (Var "a") (Var "a")), Exists TBot "a" TTop]

w8 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Person")), Sub (Fun (Nominal "Person") (Nominal "Student")) (Fun (Var "a") (Var "a")), Exists TBot "a" TTop]

w9 = [Sub (Fun (Var "a") (Var "a")) (Fun (Nominal "Person") (Nominal "Person")), Sub (Fun (Nominal "Person") (Nominal "Grad")) (Fun (Var "a") (Var "a")), Exists TBot "a" TTop]

-- New cases

w10 = [Sub (Var "b") (Var "c"), Exists (Var "a") "c" TTop, Exists TBot "b" TTop, Exists TBot "a" TTop]

w11 = [Sub (Var "c") (Var "b"), Exists TBot "c" (Var "a"), Exists TBot "b" TTop, Exists TBot "a" TTop]

w12 = [Sub (Var "c") (Nominal "Student"), Exists TBot "c" (Var "a"), Exists TBot "b" TTop, Exists TBot "a" TTop]

w13 = [Exists (Var "a") "c" (Nominal "Student"), Sub (Nominal "Tree") (Var "a"), Exists TBot "a" TTop]
