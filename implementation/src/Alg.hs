{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Alg where

import Data.List (delete, find, union)
import Data.Maybe (fromJust)
import Parser (parseExp)
import Syntax

-- Algorithmic Chain
data Chain
  = Sub Typ Typ
  | Chk Exp Typ
  | Inf Exp (Typ -> Chain)
  | Match Typ (Typ -> Typ -> Chain)
  | InfApp Typ Typ Exp (Typ -> Chain)
  | InfTApp Typ Typ (Typ -> Chain)
  | CaseChk Exp Typ Typ
  | CaseInf Typ Exp Exp (Typ -> Chain)
  | ConsInf Typ Exp (Typ -> Chain)
  | End

instance Show Chain where
  show c1 = show' c1 0
    where
      show' :: Chain -> Int -> String
      show' (Sub a b) _ = show a ++ " <: " ++ show b
      show' (Chk e t) _ = show e ++ " <== " ++ show t
      show' (Inf e c) n =
        show e ++ " ==>" ++ show n ++ " " ++ show' (c (TVar $ show n)) (n + 1)
      show' (Match a c) n =
        show a ++ " ▹" ++ show n ++ "," ++ show (n + 1) ++ " " ++ show' (c (TVar $ show n) (TVar $ show (n + 1))) (n + 2)
      show' (InfApp a b e c) n =
        show a ++ " -> " ++ show b ++ " * " ++ show e ++ " =>>" ++ show n ++ " " ++ show' (c (TVar $ show n)) (n + 1)
      show' (InfTApp a b c) n =
        show a ++ " o " ++ show b ++ " =>>" ++ show n ++ " " ++ show' (c (TVar $ show n)) (n + 1)
      show' (CaseChk e a b) _ = show e ++ " <=={" ++ show a ++ " :: List} " ++ show b
      show' (CaseInf a e e1 c) n =
        show a ++ " # " ++ show e ++ " # " ++ show e1 ++ " =>>[]" ++ show n ++ " " ++ show' (c (TVar $ show n)) (n + 1)
      show' (ConsInf a e c) n =
        show e ++ " <== [" ++ show a ++ "] ==>" ++ show n ++ " " ++ show' (c (TVar $ show n)) (n + 1)
      show' End _ = "End"

-- Worklist
type Worklist = [Work]

data Work
  = WTVar String Typ
  | WSVar String Typ
  | WEVar String
  | WBind String Typ
  | WJug Chain
  deriving (Show)

instance {-# OVERLAPPING #-} Show [Work] where
  show [] = "."
  show (WTVar x u : w) = show w ++ ", " ++ x ++ " <: " ++ show u
  show (WSVar x u : w) = show w ++ ", ~" ++ x ++ " <: " ++ show u
  show (WEVar x : w) = show w ++ ", ^" ++ x
  show (WBind x t : w) = show w ++ ", " ++ x ++ " : " ++ show t
  show (WJug c : w) = show w ++ " ||- " ++ show c

eesubst :: String -> Exp -> Exp -> Exp
eesubst s e (Lam x b)
  | s == x = Lam x b
  | otherwise = Lam x (eesubst s e b)
eesubst s e (App e1 e2) = App (eesubst s e e1) (eesubst s e e2)
eesubst s e (Ann e1 t) = Ann (eesubst s e e1) t
eesubst s e (TApp e1 t) = TApp (eesubst s e e1) t
eesubst s e (TAbs x t e1) = TAbs x t (eesubst s e e1)
eesubst s e (Var x)
  | s == x = e
  | otherwise = Var x
eesubst s e (Cons e1 e2) = Cons (eesubst s e e1) (eesubst s e e2)
eesubst s e (Case e1 e2 e3) = Case (eesubst s e e1) (eesubst s e e2) (eesubst s e e3)
eesubst s e (Fix e1) = Fix (eesubst s e e1)
eesubst s e (Let x e1 e2)
  | s == x = Let x e1 e2
  | otherwise = Let x (eesubst s e e1) (eesubst s e e2)
eesubst s e (LetA x t e1 e2)
  | s == x = LetA x t e1 e2
  | otherwise = LetA x t (eesubst s e e1) (eesubst s e e2)
eesubst _ _ t = t

esubst :: String -> Typ -> Exp -> Exp
esubst e s (Lam x b) = Lam x (esubst e s b)
esubst e s (App e1 e2) = App (esubst e s e1) (esubst e s e2)
esubst e s (Ann e1 t) = Ann (esubst e s e1) (tsubst e s t)
esubst e s (TApp e1 t) = TApp (esubst e s e1) (tsubst e s t)
esubst e s (TAbs x t e1) = TAbs x (tsubst e s t) (esubst e s e1)
esubst e s (Cons e1 e2) = Cons (esubst e s e1) (esubst e s e2)
esubst e s (Case e1 e2 e3) = Case (esubst e s e1) (esubst e s e2) (esubst e s e3)
esubst e s (Fix e1) = Fix (esubst e s e1)
esubst e s (Let x e1 e2) = Let x (esubst e s e1) (esubst e s e2)
esubst e s (LetA x t e1 e2) = LetA x (tsubst e s t) (esubst e s e1) (esubst e s e2)
esubst _ _ t = t

etsubst :: String -> Typ -> Exp -> Exp
etsubst e s (Lam x b) = Lam x (etsubst e s b)
etsubst e s (App e1 e2) = App (etsubst e s e1) (etsubst e s e2)
etsubst e s (Ann e1 t) = Ann (etsubst e s e1) (ttsubst e s t)
etsubst e s (TApp e1 t) = TApp (etsubst e s e1) (ttsubst e s t)
etsubst e s (TAbs x t e1) = TAbs x (ttsubst e s t) (etsubst e s e1)
etsubst _ _ t = t

tsubst :: String -> Typ -> Typ -> Typ
tsubst _ _ TInt = TInt
tsubst _ _ TBool = TBool
tsubst _ _ TTop = TTop
tsubst _ _ TBot = TBot
tsubst _ _ (TVar a) = TVar a
tsubst _ _ (SVar a) = SVar a
tsubst s t (EVar x)
  | s == x = t
  | otherwise = EVar x
tsubst s t (Forall a b c)
  | s == a = Forall a b c
  | otherwise = Forall a (tsubst s t b) (tsubst s t c)
tsubst s t (TArr t1 t2) =
  TArr (tsubst s t t1) (tsubst s t t2)
tsubst s t (TList t1) = TList (tsubst s t t1)

ttsubst :: String -> Typ -> Typ -> Typ
ttsubst _ _ TInt = TInt
ttsubst _ _ TBool = TBool
ttsubst _ _ TTop = TTop
ttsubst _ _ TBot = TBot
ttsubst _ _ (EVar a) = EVar a
ttsubst _ _ (SVar a) = SVar a
ttsubst s t (TVar x)
  | s == x = t
  | otherwise = TVar x
ttsubst s t (Forall a b c)
  | s == a = Forall a b c
  | otherwise = Forall a (ttsubst s t b) (ttsubst s t c)
ttsubst s t (TArr t1 t2) =
  TArr (ttsubst s t t1) (ttsubst s t t2)
ttsubst s t (TList t1) = TList (ttsubst s t t1)

csubst :: String -> Typ -> Chain -> Chain
csubst s t (Sub a b) = Sub (tsubst s t a) (tsubst s t b)
csubst s t (Chk e a) = Chk (esubst s t e) (tsubst s t a)
csubst s t (Inf e f) = Inf (esubst s t e) (csubst s t . f)
csubst s t (Match t1 f) = Match (tsubst s t t1) (\a b -> csubst s t (f a b))
csubst s t (InfApp t1 t2 e f) = InfApp (tsubst s t t1) (tsubst s t t2) (esubst s t e) (csubst s t . f)
csubst s t (InfTApp t1 t2 f) = InfTApp (tsubst s t t1) (tsubst s t t2) (csubst s t . f)
csubst s t (CaseChk e a b) = CaseChk (esubst s t e) (tsubst s t a) (tsubst s t b)
csubst s t (CaseInf t1 e e1 f) = CaseInf (tsubst s t t1) (esubst s t e) (esubst s t e1) (csubst s t . f)
csubst s t (ConsInf t1 e f) = ConsInf (tsubst s t t1) (esubst s t e) (csubst s t . f)
csubst _ _ End = End

ftv :: Typ -> [Typ]
ftv TInt = []
ftv TBool = []
ftv TTop = []
ftv TBot = []
ftv (TVar a) = [TVar a]
ftv (SVar a) = [SVar a]
ftv (EVar a) = [EVar a]
ftv (Forall a b c) = ftv b `union` delete (TVar a) (ftv c)
ftv (TArr t1 t2) = ftv t1 `union` ftv t2
ftv (TList t1) = ftv t1

genSplit :: [Char] -> ([Char], [Char])
genSplit x = (x ++ "1", x ++ "2")

findBind :: String -> Worklist -> Maybe Typ
findBind x (WBind y a : w)
  | x == y = Just a
  | otherwise = findBind x w
findBind x (_ : w) = findBind x w
findBind _ [] = Nothing

pickNewVar :: [Work] -> [Char]
pickNewVar w = [fromJust $ find (\c -> all (\var -> c `notElem` var) wvars) ['a' .. 'w']]
  where
    wvars =
      concatMap
        ( \case
            WTVar v _ -> [v]
            WSVar v _ -> [v]
            WEVar v -> [v]
            _ -> []
        )
        w

expVar :: Exp -> [String]
expVar (Var x) = [x]
expVar (Lam x b) = x : expVar b
expVar (App e1 e2) = expVar e1 ++ expVar e2
expVar (Cons e1 e2) = expVar e1 ++ expVar e2
expVar (Case e1 e2 e3) = expVar e1 ++ expVar e2 ++ expVar e3
expVar (Fix e) = expVar e
expVar _ = []

pickNewBindVar :: Foldable t => Exp -> t Work -> String
pickNewBindVar e w = fromJust $ find (`notElem` wvars) bvarsupply
  where
    wvars =
      concatMap
        ( \case
            WBind v _ -> [v]
            _ -> []
        )
        w
        ++ expVar e
    bvarsupply = "x" : "y" : [xy : show @Integer n | n <- [1 .. 100], xy <- ['x', 'y']]

tvarBound :: [Work] -> String -> Typ
tvarBound w a = head [t | WTVar a' t <- w, a == a']

svarBound :: [Work] -> String -> Typ
svarBound w a = head [t | WSVar a' t <- w, a == a']

mono :: [Work] -> Typ -> Bool
mono _ TInt = True
mono _ TBool = True
mono _ TTop = False
mono _ TBot = False
mono w (TVar a) = tvarBound w a == TTop
mono _ (EVar _) = True
mono _ (SVar _) = False
mono _ (Forall {}) = False
mono w (TArr a b) = mono w a && mono w b
mono w (TList t) = mono w t

insertEVar :: String -> String -> Worklist -> Worklist
insertEVar a b (WEVar c : w)
  | a == c = WEVar a : WEVar b : w
  | otherwise = WEVar c : insertEVar a b w
insertEVar a b (x : w) = x : insertEVar a b w
insertEVar _ _ _ = error "insert error"

substWL :: String -> Typ -> Worklist -> Worklist
substWL a t (WEVar b : w)
  | a == b = w
  | EVar b `notElem` ftv t = WEVar b : substWL a t w
  | otherwise = substWL a t (insertEVar a b w)
substWL a t (WTVar b u : w)
  | TVar b `notElem` ftv t = WTVar b (tsubst a t u) : substWL a t w
  | otherwise = error $ b ++ " ∈ FV(" ++ show t ++ ")."
substWL a t (WSVar b u : w)
  | SVar b `notElem` ftv t = WSVar b (tsubst a t u) : substWL a t w
  | otherwise = error $ show (SVar b) ++ " ∈ FV(" ++ show t ++ ")."
substWL a t (WBind x t1 : w) = WBind x (tsubst a t t1) : substWL a t w
substWL a t (WJug c : w) = WJug (csubst a t c) : substWL a t w
substWL a t w = error $ "substWL {" ++ show t ++ " / ^" ++ a ++ "} (" ++ show w ++ ") fails."

alphaEq :: Typ -> Typ -> Bool
alphaEq (Forall x1 u1 t1) (Forall x2 u2 t2) =
  alphaEq u1 u2 && alphaEq (ttsubst x1 x t1) (ttsubst x2 x t2)
  where
    x = TVar $ "$" ++ x1
alphaEq (TArr a1 b1) (TArr a2 b2) = alphaEq a1 a2 && alphaEq b1 b2
alphaEq (TList t1) (TList t2) = alphaEq t1 t2
alphaEq x y = x == y

step :: Worklist -> Worklist
-- Garbage collection
step (WTVar _ _ : w) = w
step (WSVar _ _ : w) = w
step (WEVar _ : w) = w
step (WBind _ _ : w) = w
-- Subtyping
step (WJug (Sub TInt TInt) : w) = w
step (WJug (Sub TBool TBool) : w) = w
step (WJug (Sub (TVar a) (TVar b)) : w)
  | a == b = w
step (WJug (Sub (SVar a) (SVar b)) : w)
  | a == b = w
step (WJug (Sub (EVar a) (EVar b)) : w)
  | a == b = w
step (WJug (Sub _ TTop) : w) = w
step (WJug (Sub TBot _) : w) = w
step (WJug (Sub (TArr a b) (TArr c d)) : w) = WJug (Sub c a) : WJug (Sub b d) : w
step (WJug (Sub (Forall a u1 t1) (Forall b u2 t2)) : w) = WJug (Sub t1' t2') : WJug (Sub u1 u2) : WJug (Sub u2 u1) : WSVar x u1 : w
  where
    x = pickNewVar w
    t1' = ttsubst a (SVar x) t1
    t2' = ttsubst b (SVar x) t2
step (WJug (Sub (Forall a u t1) t2) : w) = WJug (Sub t' t2) : WJug (Sub (EVar x) u) : WEVar x : w
  where
    x = pickNewVar w
    t' = ttsubst a (EVar x) t1
step (WJug (Sub (EVar a) t) : w)
  | mono w t = substWL a t w
step (WJug (Sub t (EVar a)) : w)
  | mono w t = substWL a t w
step (WJug (Sub (EVar a) (TArr b c)) : w) =
  WJug (Sub (TArr (EVar a1) (EVar a2)) (TArr b c)) : substWL a (TArr (EVar a1) (EVar a2)) (WEVar a2 : WEVar a1 : w)
  where
    (a1, a2) = genSplit a
step (WJug (Sub (TArr b c) (EVar a)) : w) =
  WJug (Sub (TArr b c) (TArr (EVar a1) (EVar a2))) : substWL a (TArr (EVar a1) (EVar a2)) (WEVar a2 : WEVar a1 : w)
  where
    (a1, a2) = genSplit a
step (WJug (Sub (TVar a) t) : w) = WJug (Sub u t) : w
  where
    u = tvarBound w a
step (WJug (Sub (SVar a) t) : w) = WJug (Sub u t) : w
  where
    u = svarBound w a

-- List subtyping
step (WJug (Sub (TList a) (TList b)) : w) = WJug (Sub a b) : w
step (WJug (Sub (EVar a) (TList b)) : w) = WJug (Sub (EVar x) b) : substWL a (TList (EVar x)) (WEVar x : w)
  where
    x = pickNewVar w
step (WJug (Sub (TList b) (EVar a)) : w) = WJug (Sub (EVar x) b) : substWL a (TList (EVar x)) (WEVar x : w)
  where
    x = pickNewVar w

-- Checking
step (WJug (Chk (Lam x e) (TArr a b)) : w) = WJug (Chk e' b) : WBind y a : w
  where
    y = pickNewBindVar e w
    e' = eesubst x (Var y) e
step (WJug (Chk (Lam x e) TTop) : w) = WJug (Chk e' TTop) : WBind y TBot : w
  where
    y = pickNewBindVar e w
    e' = eesubst x (Var y) e
step (WJug (Chk (Lam x e) (EVar a)) : w) =
  WJug (Chk e' (EVar a2)) : WBind y (EVar a1) : substWL a (TArr (EVar a1) (EVar a2)) (WEVar a2 : WEVar a1 : w)
  where
    (a1, a2) = genSplit a
    y = pickNewBindVar e w
    e' = eesubst x (Var y) e
-- type abstraction (new)
step (WJug (Chk (TAbs a u1 e) (Forall b u2 t)) : w) =
  WJug (Chk e' t') : WJug (Sub u1 u2) : WJug (Sub u2 u1) : WTVar c u2 : w
  where
    c = pickNewVar w
    e' = etsubst a (TVar c) e
    t' = ttsubst b (TVar c) t
-- List checking
step (WJug (Chk Nil (TList _)) : w) = w
step (WJug (Chk (Cons e1 e2) (TList a)) : w) = WJug (Chk e1 a) : WJug (Chk e2 (TList a)) : w
step (WJug (CaseChk e (TList a) b) : w) = WJug (Chk e (TArr a (TArr (TList a) b))) : w
step (WJug (Chk (Case e e1 e2) b) : w) = WJug (Chk e1 b) : WJug (Inf e (\a -> CaseChk e2 a b)) : w
-- Fix checking
step (WJug (Chk (Fix e) a) : w) = WJug (Chk e (TArr a a)) : w
-- Let checking
step (WJug (Chk (LetA x t e1 e2) b) : w) = WJug (Chk (App (Ann (Lam x e2) (TArr t b)) (Ann (Fix (Lam x e1)) t)) b) : w
-- Subsumption checking
step (WJug (Chk e b) : w) = WJug (Inf e (`Sub` b)) : w
-- Inference --
step (WJug (Inf (Var x) c) : w) = case findBind x w of
  Just a -> WJug (c a) : w
  Nothing -> error $ "No binding for " ++ x
step (WJug (Inf (Ann e a) c) : w) = WJug (Chk e a) : WJug (c a) : w
step (WJug (Inf (ILit _) c) : w) = WJug (c TInt) : w
step (WJug (Inf (BLit _) c) : w) = WJug (c TBool) : w
step (WJug (Inf (App e1 e2) c) : w) = WJug (Inf e1 (\b -> Match b (\d1 d2 -> InfApp d1 d2 e2 c))) : w
step (WJug (Inf (TApp e a) c) : w) = WJug (Inf e (\b -> InfTApp b a c)) : w
step (WJug (Inf (Lam x e) c) : w) =
  WJug (Chk e' (EVar b)) : WBind y (EVar a) : WJug (c (TArr (EVar a) (EVar b))) : WEVar b : WEVar a : w
  where
    a = pickNewVar w
    b = pickNewVar (WEVar a : w)
    y = pickNewBindVar e w
    e' = eesubst x (Var y) e
-- Type abstraction inference
step (WJug (Inf (TAbs a u (Ann e t)) c) : w) =
  WJug (Chk e' t') : WTVar a' u : WJug (c (Forall a' u t')) : w
  where
    a' = pickNewVar w
    e' = etsubst a (TVar a') e
    t' = ttsubst a (TVar a') t

-- Matching
step (WJug (Match (TArr a b) c) : w) = WJug (c a b) : w
step (WJug (Match TBot c) : w) = WJug (c TTop TBot) : w
step (WJug (Match (Forall a u t) c) : w) = WJug (Match t' c) : WJug (Sub (EVar x) u) : WEVar x : w
  where
    x = pickNewVar w
    t' = ttsubst a (EVar x) t
step (WJug (Match (TVar a) c) : w) = WJug (Match (tvarBound w a) c) : w
step (WJug (Match (EVar a) c) : w) =
  substWL a (TArr (EVar a1) (EVar a2)) (WJug (Match (TArr (EVar a1) (EVar a2)) c) : WEVar a2 : WEVar a1 : w)
  where
    (a1, a2) = genSplit a
-- Dummy Application Inference
step (WJug (InfApp a b e c) : w) = WJug (Chk e a) : WJug (c b) : w

-- Type application inference
step (WJug (InfTApp (Forall a u t1) t2 c) : w) = WJug (c (ttsubst a t2 t1)) : WJug (Sub t2 u) : w
step (WJug (InfTApp TBot _ c) : w) = WJug (c TBot) : w
step (WJug (InfTApp (TVar a) b c) : w) = WJug (InfTApp (tvarBound w a) b c) : w

-- list rules
step (WJug (Inf Nil c) : w) = WJug (c (Forall x TBot (TList (TVar x)))) : w
  where
    x = pickNewVar w
step (WJug (Inf (Cons e1 e2) c) : w) = WJug (Inf e1 (\b -> ConsInf b e2 c)) : w
step (WJug (Inf (Case e e1 e2) c) : w) = WJug (Inf e1 (\b -> CaseInf b e e2 c)) : w
step (WJug (ConsInf b e c) : w) = WJug (Chk e (TList b)) : WJug (c b) : w
step (WJug (CaseInf b e e2 c) : w) = WJug (Inf e (\a -> CaseChk e2 a b)) : WJug (c b) : w
-- fix
step (WJug (Inf (Fix e) c) : w) = WJug (Chk e (TArr (EVar a) (EVar a))) : WJug (c (EVar a)) : WEVar a : w
  where
    a = pickNewVar w
-- let
step (WJug (Inf (Let x e1 e2) c) : w) = WJug (Inf (App (Lam x e2) (Fix (Lam x e1))) c) : w
step (WJug (Inf (LetA x t e1 e2) c) : w) = WJug (Inf e2 c) : WJug (Chk e1 t) : WBind x t : w

-- ret
step (WJug End : w) = w
step w = error $ "No rule matching " ++ show w

runStep :: Worklist -> IO ()
runStep [] = putStrLn "Done."
runStep w = do
  print w
  runStep (step w)

run :: FilePath -> IO ()
run s = do
  code <- readFile s
  case parseExp code of
    Left err -> putStrLn err
    Right e -> runStep [WJug (Inf e (const End))]
