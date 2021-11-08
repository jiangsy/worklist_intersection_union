import Prelude hiding (flip)
import Data.List
-- import Data.Set as Set

import Debug.Trace

{- A lazy subtyping algorithm:

A,B := Int | A -> B | forall a. A 
T ::= . | T,a | T,^a | T |- A <: B

Algorithm:

T, a                               --> T                                                      (rule 1)
T[^a] |- [l1..ln] <: ^a <:[u1..um] --> T |- l1 <: u1 .... |- ln <: lm (n x m)                 (rule 2)
T |- Int <: Int                    --> T                                                      (rule 5)
T[a]  |- a <: a                    --> T                                                      (rule 6)
T[^a] |- ^a <: ^a                  --> T                                                      (rule 7)


T |- A -> B <: C -> D              --> T |- C <: A |- B <: D                                  (rule 8)
T |- forall a . B <: C             --> T,^a |- [^a/a] B <: C                                  (rule 9)
T |- A <: forall b . B             --> T,b |- A <: C                                          (rule 10)


T[lb <: ^a < ub] |- ^a <: A -> B   --> [^a1 -> ^a2/^a]_{^a1,^a2} T |- ^a1 -> ^a2 <: A -> B   
                when not monotype (A->B)  
T[lb <: ^a < ub] |- A -> B <: ^a   --> [^a1 -> ^a2/^a]_{^a1,^a2} T |- A -> B <: ^a1 -> ^a2   
                when not monotype (A->B)  

T[a][lb <: ^b < ub] |- a <: ^b     --> T[a][lb  {a} <: ^b < ub] 
                when not monotype (A->B)  
T[lb <: ^a < ub] |- A -> B <: ^a   --> [^a1 -> ^a2/^a]_{^a1,^a2} T |- A -> B <: ^a1 -> ^a2   
                when not monotype (A->B)  



T |- ^a <: t                 --> [t/^a]_{} T                                           
T |- t <: ^a                 --> [t/^a]_{} T                                           
T |- ^a <: A -> B            --> [^a1 -> ^a2/^a]_{^a1,^a2} T |- ^a1 -> ^a2 <: A -> B   
       when not monotype (A->B)  
T |- A -> B <: ^a            --> [^a1 -> ^a2/^a]_{^a1,^a2} T |- A -> B <: ^a1 -> ^a2   
       when not monotype (A->B)  



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
data Work = V (Either Int Int)  | Sub Typ Typ | Bound Typ [Typ] [Typ] deriving Eq

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
  show (Bound a lb ub)  = show lb ++  " <: " ++ show a ++ " <: " ++ show ub

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

step :: Int -> [Work] -> (Int, [Work], String)
step n (V i : ws)            = (n, ws, "Garbage Collection")     
step n (Sub TInt TInt : ws)  = (n, ws, "SInt")                
step n (Sub (TVar i) (TVar j) : ws)                             -- TODO: need to check if defined
                  | i == j   = (n, ws, "SUVar")                  
step n (Sub (TArrow a b) (TArrow c d) : ws) =
                  (n, Sub b d : Sub c a : ws, "SArrow")         
step n (Sub a (TForall g) : ws) =                               
  (n+1, Sub a (g (TVar (Left n))) : V (Left n) : ws, "SForallR")
step n (Sub (TForall g) b : ws) =                               
  (n+1, Sub (g (TVar (Right n))) b : V (Right n) : ws, "SForallL") 
step n (Sub (TVar (Right i)) a  : ws)       
  | mono a = (n, substWL i a [] ws, "SolveL")
step n (Sub a (TVar (Right i))  : ws)       
  | mono a = (n, substWL i a [] ws, "SolveL")
step n (Sub (TVar (Right i)) (TArrow a b) : ws) = (n + 2, Sub a a1 : Sub a2 b : substWL i a1_a2 [n,n+1] ws, "SplitL")
  where
    a1 = TVar (Right n)
    a2 = TVar $ Right (n + 1)
    a1_a2 = TArrow a1 a2
step n (Sub (TArrow a b) (TVar (Right i)) : ws) = (n + 2, Sub a1 a : Sub b a2 : substWL i a1_a2 [n,n+1] ws, "SplitR")
  where
    a1 = TVar $ Right n
    a2 = TVar $ Right (n + 1)
    a1_a2 = TArrow a1 a2
step n _  = error "Incorrect step()!"

check :: Int -> [Work] -> String
check n [] = "Success!"
check n ws =
  let (m,ws',s1) = step n ws
      s2         = check m ws'
  in ("   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ " \t\t\t Size: " ++ show (size ws) ++ " }\n" ++ s2)