{-# LANGUAGE FlexibleInstances, OverlappingInstances, ScopedTypeVariables #-}

import Prelude hiding (drop)
import Data.List
import Data.Maybe
import Control.Monad.Identity (fix)
-- import Foreign.C.Error (e2BIG)
import Control.Monad (liftM)
import Debug.Trace


import Data.Void
import qualified Text.Parsec as P
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Text.Megaparsec.Error

-- Algorithmic Types
data Typ =
    TInt
  | TTop
  | TBot
  | TVar String
  | SVar String
  | EVar String
  | Forall String Typ
  | TArr Typ Typ
  | TList Typ
  deriving (Eq)

instance Show Typ where
  show TInt = "Int"
  show TTop = "⊤"
  show TBot = "⊥"
  show (TVar x) = x
  show (EVar x) = "^" ++ x
  show (SVar x) = "~" ++ x
  show (Forall x t) = "(forall " ++ x ++ ". " ++ show t ++ ")"
  show (TArr a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (TList t) = "[" ++ show t ++ "]"

-- Terms
data Exp =
    Var String
  | Lit Integer
  | Lam String Exp
  | App Exp Exp
  | Ann Exp Typ
  | TApp Exp Typ
  | TAnn String Exp
  | Nil
  | Cons Exp Exp
  | Case Exp Exp Exp
  | Fix Exp
  | Let String Exp Exp
  | LetA String Typ Exp Exp
  deriving (Eq)

instance Show Exp where
  show (Var x) = x
  show (Lit n) = show n
  show (Lam x e) = "(\\" ++ x ++ " -> " ++ show e ++ ")"
  show (App e1 e2) = "(" ++ show e1 ++ " (" ++ show e2 ++ "))"
  show (Ann e t) = show e ++ " :: " ++ show t
  show (TApp e t) = show e ++ " @ " ++ show t
  show (TAnn x e) = "(/\\" ++ x ++ ". " ++ show e ++ ")"
  show Nil = "[]"
  show (Cons e1 e2) = show e1 ++ " : " ++ show e2
  show (Case e e1 e2) = "case " ++ show e ++ " of [] -> " ++ show e1 ++ "; " ++ show e2
  show (Fix e) = "(fix " ++ show e ++ ")"
  show (Let x e1 e2) = "let " ++ x ++ " = " ++ show e1 ++ " in " ++ show e2
  show (LetA x t e1 e2) = "let " ++ x ++ " : " ++ show t ++ " = " ++ show e1 ++ " in " ++ show e2

-- Algorithmic Chain
data Chain =
    Sub Typ Typ
  | Chk Exp Typ
  | Inf Exp (Typ -> Chain)
  | AInf Typ Exp (Typ -> Chain)
  | ATyp Typ Typ (Typ -> Chain)
  | LChk Exp Typ Typ
  | LInf Typ Exp Exp (Typ -> Chain)
  | Ret Typ

instance Show Chain where
  show c = show' c 0
    where
      show' (Sub a b) _ = show a ++ " <: " ++ show b
      show' (Chk e t) _ = show e ++ " <== " ++ show t
      show' (Inf e c) n = show e ++ " ==>" ++ show n ++ " " ++
                            show' (c (TVar $ show n)) (n + 1)
      show' (AInf a e c) n = show a ++ " * " ++ show e ++ " =>>" ++ show n ++ " " ++
                            show' (c (TVar $ show n)) (n + 1)
      show' (ATyp a b c) n = show a ++ " o " ++ show b ++ " =>>" ++ show n ++ " " ++
                            show' (c (TVar $ show n)) (n + 1)
      show' (LChk e a b) n = "" ++ show e ++ " <=={" ++ show a ++ " :: List} " ++ show b
      show' (LInf a e e1 c) n = show a ++ " # " ++ show e ++ " # " ++ show e1 ++ " =>>[]" ++ show n ++ " " ++
                            show' (c (TVar $ show n)) (n + 1)
      show' (Ret t) n = "Ret " ++ show t

-- Worklist
type Worklist = [Work]
data Work =
    WTVar String
  | WSVar String
  | WEVar String
  | WBind String Typ
  | WJug Chain
  deriving Show

instance Show [Work] where
  show [] = "."
  show (WTVar x : w) = show w ++ ", " ++ x
  show (WSVar x : w) = show w ++ ", ~" ++ x
  show (WEVar x : w) = show w ++ ", ^" ++ x
  show (WBind x t : w) = show w ++ ", " ++ x ++ " : " ++ show t
  show (WJug c : w) = show w ++ " ||- " ++ show c


eesubst :: String -> Exp -> Exp -> Exp
eesubst s e (Lam x b)
  | s == x    = Lam x b
  | otherwise = Lam x (eesubst s e b)
eesubst s e (App e1 e2) = App (eesubst s e e1) (eesubst s e e2)
eesubst s e (Ann e1 t) = Ann (eesubst s e e1) t
eesubst s e (TApp e1 t) = TApp (eesubst s e e1) t
eesubst s e (TAnn x e1) = TAnn x (eesubst s e e1)
eesubst s e (Var x)
  | s == x    = e
  | otherwise = Var x
eesubst s e (Cons e1 e2) = Cons (eesubst s e e1) (eesubst s e e2)
eesubst s e (Case e1 e2 e3) = Case (eesubst s e e1) (eesubst s e e2) (eesubst s e e3)
eesubst s e (Fix e1) = Fix (eesubst s e e1)
eesubst s e (Let x e1 e2)
  | s == x    = Let x e1 e2
  | otherwise = Let x (eesubst s e e1) (eesubst s e e2)
eesubst s e t = t

esubst :: String -> Typ -> Exp -> Exp
esubst e s (Lam x b) = Lam x (esubst e s b)
esubst e s (App e1 e2) = App (esubst e s e1) (esubst e s e2)
esubst e s (Ann e1 t) = Ann (esubst e s e1) (tsubst e s t)
esubst e s (TApp e1 t) = TApp (esubst e s e1) (tsubst e s t)
esubst e s (TAnn x e1) = TAnn x (esubst e s e1)
esubst e s (Cons e1 e2) = Cons (esubst e s e1) (esubst e s e2)
esubst e s (Case e1 e2 e3) = Case (esubst e s e1) (esubst e s e2) (esubst e s e3)
esubst e s (Fix e1) = Fix (esubst e s e1)
esubst e s (Let x e1 e2) = Let x (esubst e s e1) (esubst e s e2)
esubst e s t = t

etsubst :: String -> Typ -> Exp -> Exp
etsubst e s (Lam x b) = Lam x (etsubst e s b)
etsubst e s (App e1 e2) = App (etsubst e s e1) (etsubst e s e2)
etsubst e s (Ann e1 t) = Ann (etsubst e s e1) (ttsubst e s t)
etsubst e s (TApp e1 t) = TApp (etsubst e s e1) (ttsubst e s t)
etsubst e s (TAnn x e1) = TAnn x (etsubst e s e1)
etsubst e s (Cons e1 e2) = Cons (etsubst e s e1) (etsubst e s e2)
etsubst e s (Case e1 e2 e3) = Case (etsubst e s e1) (etsubst e s e2) (etsubst e s e3)
etsubst e s (Fix e1) = Fix (etsubst e s e1)
etsubst e s (Let x e1 e2) = Let x (etsubst e s e1) (etsubst e s e2)
etsubst e s t = t

tsubst :: String -> Typ -> Typ -> Typ
tsubst s t TInt = TInt
tsubst s t TTop = TTop
tsubst s t TBot = TBot
tsubst s t (TVar a) = TVar a
tsubst s t (SVar a) = SVar a
tsubst s t (EVar x)
  | s == x     = t
  | otherwise  = EVar x
tsubst s t (Forall a b)
  | s == a     = Forall a b
  | otherwise  = Forall a (tsubst s t b)
tsubst s t (TArr t1 t2) =
  TArr (tsubst s t t1) (tsubst s t t2)
tsubst s t (TList t1) = TList (tsubst s t t1)

ttsubst :: String -> Typ -> Typ -> Typ
ttsubst s t TInt = TInt
ttsubst s t TTop = TTop
ttsubst s t TBot = TBot
ttsubst s t (EVar a) = EVar a
ttsubst s t (SVar a) = SVar a
ttsubst s t (TVar x)
  | s == x     = t
  | otherwise  = TVar x
ttsubst s t (Forall a b)
  | s == a     = Forall a b
  | otherwise  = Forall a (ttsubst s t b)
ttsubst s t (TArr t1 t2) =
  TArr (ttsubst s t t1) (ttsubst s t t2)
ttsubst s t (TList t1) = TList (ttsubst s t t1)

csubst :: String -> Typ -> Chain -> Chain
csubst s t (Sub a b) = Sub (tsubst s t a) (tsubst s t b)
csubst s t (Chk e a) = Chk (esubst s t e) (tsubst s t a)
csubst s t (Inf e f) = Inf (esubst s t e) (\t1 -> csubst s t (f t1))
csubst s t (AInf t1 e f) = AInf (tsubst s t t1) (esubst s t e) (\t1 -> csubst s t (f t1))
csubst s t (ATyp t1 t2 f) = ATyp (tsubst s t t1) (tsubst s t t2) (\t1 -> csubst s t (f t1))
csubst s t (LChk e a b) = LChk (esubst s t e) (tsubst s t a) (tsubst s t b)
csubst s t (LInf t1 e e1 f) = LInf (tsubst s t t1) (esubst s t e) (esubst s t e1) (\t1 -> csubst s t (f t1))
csubst s t (Ret t1) = Ret (tsubst s t t1)

-- substitute a existential variable by its solution and replace its declaration by xs
wsubst :: String -> [String] -> Typ -> Worklist -> Worklist
wsubst s xs t = concatMap wsubst1
  where
    wsubst1 (WTVar x)   = [WTVar x]
    wsubst1 (WSVar x)   = [WSVar x]
    wsubst1 (WEVar x)
      | s == x    = reverse $ map WEVar xs
      | otherwise = [WEVar x]
    wsubst1 (WBind x a) = [WBind x (tsubst s t a)]
    wsubst1 (WJug c)    = [WJug (csubst s t c)]

ftv :: Typ -> [Typ]
ftv TInt = []
ftv TTop = []
ftv TBot = []
ftv (TVar a) = [TVar a]
ftv (SVar a) = [SVar a]
ftv (EVar x) = [EVar x]
ftv (Forall a b) = delete (TVar a) (ftv b)
ftv (TArr t1 t2) = union (ftv t1) (ftv t2)
ftv (TList t1) = ftv t1

{-
wsubst _ _ _ Empty = Empty
wsubst s xs t (ConsTVar w x)   = ConsTVar (wsubst s xs t w) x
wsubst s xs t (ConsEVar w x)
  | s == x    = foldr (\x w -> ConsEVar w x) (wsubst s xs t w) xs
  | otherwise = ConsEVar (wsubst s xs t w) x
wsubst s xs t (ConsBind w x a) = ConsBind (wsubst s xs t w) x (tsubst s t a)
wsubst s xs t (ConsJug w c)    = ConsJug (wsubst s xs t w) (csubst s t c)

replace :: String -> String -> String -> Worklist -> Worklist
replace a a1 a2 Empty           = Empty
replace a a1 a2 (ConsTVar l s)  = ConsTVar (replace a a1 a2 l) s 
replace a a1 a2 (ConsEVar l s)
  | s == a     = ConsEVar (ConsEVar l a1) a2
  | otherwise  = ConsEVar (replace a a1 a2 l) s
replace a a1 a2 (ConsBind l s t)  =
  ConsBind (replace a a1 a2 l) s t -- (tsubst a (TArr (TVar a1) (TVar a2)) t)
replace a a1 a2 (ConsJug l c)  =
  ConsJug (replace a a1 a2 l) c -- (csubst a (TArr (TVar a1) (TVar a2)) c) 

drop :: String -> Worklist -> Worklist
drop s Empty            = Empty
drop s (ConsTVar w x)   
  | s == x              = w
  | otherwise           = ConsTVar (drop s w) x
drop s (ConsBind w x t) = (ConsBind (drop s w) x t)
drop s (ConsJug w c)    = ConsJug (drop s w) c
drop s (ConsEVar w x)
  | s == x              = w
  | otherwise           = ConsEVar (drop s w) x
--}

-- Is `^a` declared before `^b`?
prec :: Worklist -> String -> String -> Bool
prec w a b = elem a . dropWhile (/= b) $ wex
  where
    wex = concatMap (\x -> case x of
        WEVar v -> [v]
        WTVar v -> [v]
        _       -> []
      ) w


genSplit :: [Char] -> ([Char], [Char])
genSplit x = (x ++ "1", x ++ "2")

findBind :: String -> Worklist -> Maybe Typ
findBind x (WBind y a : w)
  | x == y    = Just a
  | otherwise = findBind x w
findBind x (_ : w) = findBind x w
findBind _ [] = Nothing

pickNewVar w = [fromJust $ find (\c -> all (\var -> c `notElem` var) wvars) ['a'..'w']]
  where
    wvars = concatMap (\x -> case x of
        WTVar v -> [v]
        WSVar v -> [v]
        WEVar v -> [v]
        _ -> []
      ) w

expVar :: Exp -> [String]
expVar (Var x) = [x]
expVar (Lam x b) = x : expVar b
expVar (App e1 e2) = expVar e1 ++ expVar e2
expVar (Cons e1 e2) = expVar e1 ++ expVar e2
expVar (Case e1 e2 e3) = expVar e1 ++ expVar e2 ++ expVar e3
expVar (Fix e) = expVar e
expVar _ = []

pickNewBindVar e w = fromJust $ find (`notElem` wvars) bvarsupply
  where
    wvars = concatMap (\x -> case x of
        WBind v _ -> [v]
        _ -> []
      ) w ++ expVar e
    bvarsupply = "x" : "y" : [ xy : show n | n <- [1..100], xy <- ['x', 'y'] ]

step :: Worklist -> Worklist
-- First 4 rules
step (WTVar a : w) = w
step (WEVar a : w) = w
step (WSVar a : w) = w
step (WBind x t : w) = w

-- Subtyping --
-- Rules 5 to 9 and 13, 16 and 17
step (WJug (Sub TInt TInt) : w) = w
step (WJug (Sub (TVar a) (TVar b)) : w)
  | a == b    = w
  | otherwise = error "6"
step (WJug (Sub (SVar a) (SVar b)) : w)
  | a == b    = w
  | otherwise = error "7"
step (WJug (Sub (EVar a) (EVar b)) : w)
  | a == b     = w
  | prec w a b = wsubst b [] (EVar a) w -- rule 16
  | otherwise  = wsubst a [] (EVar b) w -- rule 17
-- Rules 18 to 21
step (WJug (Sub (TVar a) (EVar b)) : w)
  | prec w a b = wsubst b [] (TVar a) w
  | otherwise  = error "18"
step (WJug (Sub (EVar b) (TVar a)) : w)
  | prec w a b = wsubst b [] (TVar a) w
  | otherwise  = error "19"
step (WJug (Sub TInt (EVar b)) : w) = wsubst b [] TInt w
step (WJug (Sub (EVar b) TInt) : w) = wsubst b [] TInt w
-- rule 8 and 9
step (WJug (Sub _ TTop) : w) = w
step (WJug (Sub TBot _) : w) = w
-- rule 10
step (WJug (Sub (TArr a b) (TArr c d)) : w) = WJug (Sub c a) : WJug (Sub b d) : w
-- rules 12 and 11
step (WJug (Sub (Forall a t1) (Forall b t2)) : w) = WJug (Sub t1' t2') : WSVar x : w
    where
      x = pickNewVar w
      t1' = ttsubst a (SVar x) t1
      t2' = ttsubst b (SVar x) t2
step (WJug (Sub (Forall a t1) t2) : w) = WJug (Sub t' t2) : WEVar x : w
    where
      x = pickNewVar w
      t' = ttsubst a (EVar x) t1
-- rules 14 and 15
step (WJug (Sub (EVar a) (TArr b c)) : w)
  | EVar a `notElem` ftv (TArr b c) = let (a1, a2) = genSplit a
      in wsubst a [a1, a2] (TArr (EVar a1) (EVar a2)) $ WJug (Sub (EVar a) (TArr b c)) : w
  | otherwise = error "10"
step (WJug (Sub (TArr b c) (EVar a)) : w)
  | EVar a `notElem` ftv (TArr b c) = let (a1, a2) = genSplit a
      in wsubst a [a1, a2] (TArr (EVar a1) (EVar a2)) $ WJug (Sub (TArr b c) (EVar a)) : w
  | otherwise = error "11"
-- list rules
step (WJug (Sub (TList a) (TList b)) : w) = WJug (Sub a b) : w
step (WJug (Sub (EVar a) (TList b)) : w) = wsubst a [x] (TList (EVar x)) $ WJug (Sub (EVar x) b) : w
    where x = pickNewVar w
step (WJug (Sub (TList b) (EVar a)) : w) = wsubst a [x] (TList (EVar x)) $ WJug (Sub b (EVar x)) : w
    where x = pickNewVar w

-- Checking --
-- rules 23 to 26
step (WJug (Chk (Lam x e) (TArr a b)) : w) = WJug (Chk e' b) : WBind y a : w
    where
      y = pickNewBindVar e w
      e' = eesubst x (Var y) e
step (WJug (Chk (Lam x e) (EVar a)) : w) = let (a1, a2) = genSplit a
      in wsubst a [a1, a2] (TArr (EVar a1) (EVar a2)) $
        WJug (Chk e' (EVar a2)) : WBind y (EVar a1) : w
    where
      y = pickNewBindVar e w
      e' = eesubst x (Var y) e
step (WJug (Chk e TTop) : w) = w
-- type abstraction (new)
-- will `a` appear in `e`?
step (WJug (Chk (TAnn a e) (Forall b t)) : w)
  | a == b = WJug (Chk e' t') : WTVar c : w
  | otherwise = error "typ abs"
    where
      c = pickNewVar w
      e' = etsubst a (TVar c) e
      t' = ttsubst a (TVar c) t
-- list rules
step (WJug (Chk (Cons e1 e2) (TList a)) : w) = WJug (Chk e1 a) : WJug (Chk e2 (TList a)) : w
step (WJug (LChk e (TList a) b) : w) = WJug (Chk e (TArr a (TArr (TList a) b))) : w
step (WJug (Chk (Case e e1 e2) b) : w) = WJug (Chk e1 b) : WJug (Inf e (\a -> LChk e2 a b)) : w
-- fix rule
step (WJug (Chk (Fix e) a) : w) = WJug (Chk e (TArr a a)) : w
-- let rule
step (WJug (Chk (Let x e1 e2) b) : w) = WJug (Chk (App (Lam x e2) (Fix (Lam x e1))) b) : w
step (WJug (Chk (LetA x t e1 e2) b) : w) = WJug (Chk (App (Ann (Lam x e2) (TArr t (EVar a))) (Ann (Fix (Lam x e1)) t)) b) : WEVar a : w
    where
      a = pickNewVar w
-- rule 22
step (WJug (Chk e b) : w) = WJug (Inf e (\a -> Sub a b)) : w

-- Inference --
step (WJug (Inf (Var x) c) : w) = case findBind x w of
    Just a  -> WJug (c a) : w
    Nothing -> error $ "No binding for " ++ x
step (WJug (Inf (Ann e a) c) : w) = WJug (Chk e a) : WJug (c a) : w

step (WJug (Inf (Lit _) c) : w) = WJug (c TInt) : w
step (WJug (Inf (Lam x e) c) : w) = WJug (Chk e' (EVar b)) : WBind y (EVar a) :
      WJug (c (TArr (EVar a) (EVar b))) : WEVar b : WEVar a : w
    where
      a = pickNewVar w
      b = pickNewVar (WEVar a : w)
      y = pickNewBindVar e w
      e' = eesubst x (Var y) e
step (WJug (Inf (App e1 e2) c) : w) = WJug (Inf e1 (\b -> AInf b e2 c)) : w
step (WJug (Inf (TApp e a) c) : w) = WJug (Inf e (\b -> ATyp b a c)) : w

step (WJug (ATyp (Forall a t1) t2 c) : w) = WJug (c (ttsubst a t2 t1)) : w
step (WJug (ATyp TBot t c) : w) = WJug (c TBot) : w

-- Application Inference --
step (WJug (AInf (Forall a t) e c) : w) = WJug (AInf t' e c) : WEVar x : w
    where
      x = pickNewVar w
      t' = ttsubst a (EVar x) t
step (WJug (AInf (TArr a b) e c) : w) = WJug (Chk e a) : WJug (c b) : w
step (WJug (AInf TBot _ c) : w) = WJug (c TBot) : w
step (WJug (AInf (EVar a) e c) : w) = let (a1, a2) = genSplit a
      in wsubst a [a1, a2] (TArr (EVar a1) (EVar a2)) $ WJug (AInf (EVar a) e c) : w

-- list rules
step (WJug (Inf Nil c) : w) = WJug (c (Forall x (TList (TVar x)))) : w
    where x = pickNewVar w
step (WJug (Inf (Cons e1 e2) c) : w) = WJug (Inf e1 (\a -> Chk e2 (TList a))) : w
step (WJug (Inf (Case e e1 e2) c) : w) = WJug (Inf e1 (\b -> LInf b e e2 c)) : w
step (WJug (LInf b e e2 c) : w) = WJug (Inf e (\a -> LChk e2 a b)) : WJug (c b) : w
-- fix
step (WJug (Inf (Fix e) c) : w) = WJug (Chk e (TArr (EVar a) (EVar a))) : WJug (c (EVar a)) : WEVar a : w
    where a = pickNewVar w
-- let
step (WJug (Inf (Let x e1 e2) c) : w) = WJug (Inf (App (Lam x e2) (Fix (Lam x e1))) c) : w
step (WJug (Inf (LetA x t e1 e2) c) : w) = WJug (Inf (App (Ann (Lam x e2) (TArr t (EVar a))) (Ann (Fix (Lam x e1)) t)) c) : WEVar a : w
    where a = pickNewVar w
-- ret
step (WJug (Ret _) : w) = w

runStep :: Worklist -> IO ()
runStep [] = putStrLn "Done."
runStep w = do
  print w
  runStep (step w)

-- Sample worklists
ta = TVar "a"
tb = TVar "b"

success1 = [WJug (Sub (Forall "a" (TArr ta TInt)) (TArr (Forall "a" (TArr ta ta)) TInt))]

failure1 = [WJug (Sub (Forall "a" (TArr TInt ta)) (TArr TInt (Forall "b" tb)))]

lamId = Lam "x" (Var "x")
litNum = Lit 33

typing1 = [WJug (Chk (App lamId litNum) TInt)]

typing2 = [WJug (Chk (
    App (App lamId lamId) litNum
  ) TInt)]


f :: [a] -> [a]
f (xs::[a]) = reverse xs :: [a]

g :: [a -> a] -> [a -> a]
g (xs::[a -> b]) = reverse xs :: [b -> b]

g' (xs::[a -> b]) = reverse xs :: [b -> a]

fex :: forall a. [a] -> [a]
fex xs = ys ++ ys
     where
       ys :: [a]
       ys = reverse xs

exList1 = [WJug (Sub (TList (Forall "a" (TArr ta TInt))) (TList (TArr (Forall "a" (TArr ta ta)) TInt)))]
exList2 = [WJug (Sub (TArr (Forall "a" (TArr ta ta)) TInt) (TArr (Forall "b" (TArr (TList tb) (TList tb))) TInt))] -- failure
exList3 = [WJug (Sub (Forall "a" (TArr ta ta)) (TArr (TList TInt) (TList TInt)))]
exList4 = [WJug (Inf Nil (\x -> Sub x x)), WTVar "a"]
exList5 = [WJug (Chk (Cons lamId (Cons (Ann lamId (TArr TInt TInt)) Nil)) (TList (TArr TInt TInt))), WTVar "a"]
exList6 = [WJug (Inf (Cons lamId (Cons (Ann lamId (TArr TInt TInt)) Nil)) (\x -> Sub x x)), WTVar "a"]

exCase1 = [WJug (Chk (Case (Cons (Lit 33) Nil) (Lit 0) (Lam "x" (Lam "xs" (Var "x")))) TInt)]
exCase2 = [WJug (Chk (Case (Cons (Lit 33) (Lit 22)) (Lit 0) (Lam "x" (Lam "xs" (Var "x")))) TInt)]

mapTyp = Forall "a" (Forall "b" (TArr (TArr ta tb)  (TArr (TList ta) (TList tb))))
mapFun = Lam "f" (Lam "xs" (
    Case (Var "xs")
         Nil
         (Lam "y" (Lam "ys"
             (Cons
                 (App (Var "f") (Var "y"))
                 (App (App (Var "rec") (Var "f")) (Var "ys")))))))
mapJug = [WJug (Inf (Ann (Fix (Lam "rec" (TAnn "a" (TAnn "b" mapFun)))) mapTyp) Ret)]

plusTyp = TArr TInt (TArr TInt TInt)
plusFun = Lam "x" (Lam "y" (Var "x"))

exLet = [WJug (Inf (Let "x" (Lit 1) (Cons (Var "x") (Cons (Lit 2) Nil))) Ret)]
mapFun' = Lam "f" (Lam "xs" (
    Case (Var "xs")
         Nil
         (Lam "y" (Lam "ys"
             (Cons
                 (App (Var "f") (Var "y"))
                 (App (App (Var "map") (Var "f")) (Var "ys")))))))
letMapIn = LetA "map" mapTyp (TAnn "a" (TAnn "b" mapFun'))
succFun = App plusFun (Lit 1)

succJug = [WJug (Inf succFun Ret)]
mapJug1 = [WJug (Inf (letMapIn (Let "succ" succFun (App (App (Var "map") (Var "succ")) (Cons (Lit 1) (Cons (Lit 2) Nil))))) Ret)]

run :: String -> IO ()
run s =
  case runParser (whole expr) "" s of
    Left err -> print $ errorBundlePretty err
    Right e -> runStep [WJug (Inf e Ret)]

-- Parsing

type Parser = Parsec Void String

parseExp :: String -> Either String Exp
parseExp s =
  case runParser (whole expr) "" s of
    Left err -> Left $ errorBundlePretty err
    Right e -> Right e

whole :: Parser a -> Parser a
whole p = sc *> p <* eof

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

expr :: Parser Exp
expr = makeExprParser term pOperators

term :: Parser Exp
term = postfixChain factor (try bapp <|> fapp)

fapp :: Parser (Exp -> Exp)
fapp = do
  e <- factor
  return (`App` e)

bapp :: Parser (Exp -> Exp)
bapp = do
  symbol "@"
  e <- atype
  return (`TApp` e)

factor :: Parser Exp
factor = postfixChain atom annOperator

annOperator :: Parser (Exp -> Exp)
annOperator = do
  symbol "::"
  t <- pType
  return (`Ann` t)

atom :: Parser Exp
atom =
  choice
    [ pLambda
    , pCase
    , pFix
    , Var <$> identifier
    , Lit <$> int
    , Nil <$ symbol "[]"
    , parens expr
    ]

pLambda :: Parser Exp
pLambda = do
  symbol "\\"
  x <- identifier
  symbol "->"
  e <- expr
  return $ Lam x e

pFix :: Parser Exp
pFix = do
  rword "fix"
  Fix <$> expr

pList :: Parser Exp
pList = undefined 

pCase :: Parser Exp
pCase = do
  rword "case"
  e <- expr
  rword "of"
  symbol "[]"
  symbol "->"
  e1 <- expr
  symbol ";"
  symbol "("
  x <- identifier
  symbol ":"
  xs <- identifier
  symbol ")"
  symbol "->"
  e2 <- expr
  return $ Case e e1 (Lam x (Lam xs e2))

pOperators :: [[Operator Parser Exp]]
pOperators = [[InfixR (Cons <$ symbol ":")]]

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

pType :: Parser Typ
pType = makeExprParser atype tOperators

tOperators :: [[Operator Parser Typ]]
tOperators = [[InfixR (TArr <$ symbol "->")]]

atype :: Parser Typ
atype =
  choice
    [pForall, TVar <$> identifier, tconst, listType, parens pType]

pForall :: Parser Typ
pForall = do
  rword "forall"
  x <- identifier
  symbol "."
  t <- pType
  return $ Forall x t

tconst :: Parser Typ
tconst =
  choice
    [ TInt <$ rword "Int"
    , TTop <$ rword "Top"
    , TBot <$ rword "Bot"]

listType :: Parser Typ
listType = do
  symbol "["
  t <- pType
  symbol "]"
  return $ TList t

------------------------------------------------------------------------
-- Misc
------------------------------------------------------------------------

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

int :: Parser Integer
int = L.decimal

-- colon :: Parser String
-- colon = symbol ":"

-- comma :: Parser String
-- comma = symbol ","

-- vdash :: Parser String
-- vdash = symbol "||-"

rword :: String -> Parser ()
rword w = string w *> notFollowedBy alphaNumChar *> sc

postfixChain :: Parser a -> Parser (a -> a) -> Parser a
postfixChain p op = do
  x <- p
  rest x
  where
    rest x =
      (do f <- op
          rest $ f x) <|>
      return x

rws :: [String] -- list of reserved words
rws = ["forall", "case", "of", "fix"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p = (:) <$> lowerChar <*> many identChar
    check x =
      if x `elem` rws
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

identChar :: Parser Char
identChar = alphaNumChar <|> oneOf "_'"
