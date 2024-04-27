import Debug.Trace
​
data Typ = TInt | Fun Typ Typ | Var Int | Nominal String deriving (Eq)
​
data Work = Exists [Typ] [Typ] | Sub Typ Typ
​
type WorkList = [Work]
​
type NominalEnv = [(String, Maybe String)]
​
instance Show Typ where
   show TInt          = "I"
   show (Fun a b)     = "(" ++ show a ++ ") -> " ++ show b
   show (Var i)       = "^" ++ show i
   show (Nominal s)   = s
​
showWork (Sub t1 t2)       _  = show t1 ++ " <: " ++ show t2
showWork (Exists ts1 ts2)  i  = show ts1 ++ " <: ^" ++ show i ++ " <: " ++ show ts2
​
instance {-# OVERLAPPING #-} Show WorkList where
   show []      = "."
   show [x]     = showWork x 0
   show (x:xs)  = show xs ++ ", " ++ showWork x (length xs)
​
subst :: Int -> Typ -> Bool -> WorkList -> WorkList
subst i t b o@(Sub t1 t2 : ws)       =  Sub t1 t2 : subst i t b ws  
subst i t b (Exists ts1 ts2 : ws)
   | i == length ws = if b then Exists ts1 (t:ts2) : ws else Exists (t:ts1) ts2 : ws
   | otherwise      = Exists ts1 ts2 : subst i t b ws   -- not fully correct as I ignore dependencies (but we know how to deal with this)
​
-- I know that the two nominal types are different
​
subN :: String -> String -> NominalEnv -> Bool
subN n1 n2 []             = False
subN n1 n2 ((n3,Nothing):es)
   | n1 /= n3 && n2 /= n3 = subN n1 n2 es
   | otherwise            = False
subN n1 n2 ((n3,Just n4):es)
   | n1 == n3 && n2 == n4 = True
   | otherwise            = subN (if n1 == n3 then n4 else n1) n2 es
​
solvable :: NominalEnv -> WorkList -> Bool
solvable _ []                                      = True
-- Subtyping
solvable e o@(Sub TInt TInt : ws)                  = trace (show o) $ solvable e ws
solvable e o@(Sub (Fun t1 t2) (Fun t3 t4) : ws)    = trace (show o) $ solvable e (Sub t3 t1 : Sub t2 t4 : ws)
solvable e o@(Sub (Var i) t1 : ws)                 = trace (show o) $ solvable e (subst i t1 True ws)
solvable e o@(Sub t1 (Var i) : ws)                 = trace (show o) $ solvable e (subst i t1 False ws)
solvable e o@(Sub (Nominal n1) (Nominal n2) : ws)
   | n1 == n2 || subN n1 n2 e = trace (show o) $ solvable e ws
   | otherwise                = False
-- Existentials
solvable e o@(Exists (t1:t2:ts1) ts2 : ws)         = trace (show o) $
   solvable e (Sub t1 t2 : Exists (t2:ts1) ts2 : ws) || (trace "Backtrack: " $ solvable e (Sub t2 t1 : Exists (t1:ts1) ts2 : ws))
solvable e o@(Exists ts1 (t1:t2:ts2) : ws)         = trace (show o) $
   solvable e (Sub t1 t2 : Exists ts1 (t1:ts2) : ws) ||  (trace "Backtrack: " $ solvable e (Sub t2 t1 : Exists ts1 (t2:ts2) : ws))
solvable e o@(Exists [t1] [t2] : ws)               = trace (show o) $ solvable e (Sub t1 t2 : ws) 
solvable e o@(Exists _ _ : ws)                     = trace (show o) $ solvable e ws
solvable e o                                       = trace (show o) $ False
​
w1 = [Sub TInt TInt, Exists [] []]
​
w2 = [Sub (Var 0) TInt, Exists [] []]
​
w3 = [Sub (Var 0) (Fun TInt TInt), Sub (Var 0) TInt, Exists [] []]
​
w4 = [Exists [Fun (Var 0) (Var 0), Fun (Fun TInt TInt) (Fun TInt TInt)] [], Exists [Fun (Var 0) (Var 0),Fun TInt TInt] [], Exists [] []]
​
nomEnv = [("Grad", Just "Student"), ("Student", Just "Person"), ("Person", Nothing)]
​
w5 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Person") (Nominal "Student")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Person") (Nominal "Person")] [], Exists [] []]
​
w6 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Person") (Nominal "Student")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Student") (Nominal "Person")] [], Exists [] []]
​
w7 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Student") (Nominal "Student")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Person") (Nominal "Person")] [], Exists [] []]
​
w8 = [Exists [Fun (Var 0) (Var 0), Fun (Nominal "Person") (Nominal "Grad")] [], Exists [Fun (Var 0) (Var 0),Fun (Nominal "Student") (Nominal "Person")] [], Exists [] []]