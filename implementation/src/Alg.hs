{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Alg where

import Data.List (delete, union)
import Parser (parseExp)
import Syntax

-- Algorithmic Judgment
data Judgment
  = Sub Typ Typ
  | Chk Exp Typ
  | Inf Exp String Judgment
  | InfAbs Typ String String Judgment
  | InfApp Typ Typ Exp String Judgment
  | InfProj Typ Typ Typ String Judgment
  | InfTApp Typ Typ String Judgment
  | CaseChk Exp Typ Typ
  | CaseInf Typ Exp Exp String Judgment
  | ConsInf Typ Exp String Judgment
  | LetInf String Typ Exp String Judgment
  | End

showJudgment :: Judgment -> String
showJudgment (Sub t1 t2) = show t1 ++ " ≤ " ++ show t2
showJudgment (Chk e t) = show e ++ " ⇐ " ++ show t
showJudgment (Inf e a c) =
  show e ++ " ⇒" ++ a ++ " " ++ showJudgment c
showJudgment (InfAbs t a b c) =
  show t ++ " ▹" ++ a ++ "," ++ b ++ " " ++ showJudgment c
showJudgment (InfApp t1 t2 e a c) =
  show t1 ++ " → " ++ show t2 ++ " ⊙ " ++ show e ++ " ➤" ++ a ++ " " ++ showJudgment c
showJudgment (InfProj t1 t2 t3 a c) =
  show t1 ++ " → " ++ show t2 ++ " ⊗ " ++ show t3 ++ " ➤" ++ a ++ " " ++ showJudgment c
showJudgment (InfTApp t1 t2 a c) =
  show t1 ++ " o " ++ show t2 ++ " ➤" ++ a ++ " " ++ showJudgment c
showJudgment (CaseChk e t1 t2) = show e ++ " ⇐{" ++ show t1 ++ " :: List} " ++ show t2
showJudgment (CaseInf t e1 e2 a c) =
  show t ++ " # " ++ show e1 ++ " # " ++ show e2 ++ " ➤[]" ++ a ++ " " ++ showJudgment c
showJudgment (ConsInf t e a c) =
  show e ++ " ⇐ [" ++ show t ++ "] ⇒" ++ a ++ " " ++ showJudgment c
showJudgment (LetInf x t e a c) =
  "let " ++ x ++ " :: " ++ show t ++ " in " ++ show e ++ " 🠶 " ++ showJudgment c
showJudgment End = "End"

instance Show Judgment where
  show c = showJudgment c

-- Worklist
type Worklist = [Work]

data TBind = TVarBind | STVarBind | ETVarBind deriving (Eq)

instance Show TBind where
  show TVarBind = "□"
  show STVarBind = "■"
  show ETVarBind = "⬒"

data Work
  = WTVar String TBind
  | WVar String Typ
  | WJug Judgment
  deriving (Show)

instance {-# OVERLAPPING #-} Show [Work] where
  show [] = "⋅"
  show (WTVar x b : w) = show w ++ ", " ++ x ++ " : " ++ show b
  show (WVar x t : w) = show w ++ ", " ++ x ++ " : " ++ show t
  show (WJug c : w) = show w ++ " ⊩ " ++ show c

eesubst :: String -> Exp -> Exp -> Exp
eesubst _ _ (ILit n) = ILit n
eesubst _ _ (BLit n) = BLit n
eesubst sx se (Lam x b)
  | sx == x = Lam x b
  | otherwise = Lam x (eesubst sx se b)
eesubst sx se (App e1 e2) = App (eesubst sx se e1) (eesubst sx se e2)
eesubst sx se (Ann e1 t) = Ann (eesubst sx se e1) t
eesubst sx se (TApp e1 t) = TApp (eesubst sx se e1) t
eesubst sx se (TAbs x e1) = TAbs x (eesubst sx se e1)
eesubst sx se (Var x)
  | sx == x = se
  | otherwise = Var x
eesubst _ _ Nil = Nil
eesubst sx se (Cons e1 e2) = Cons (eesubst sx se e1) (eesubst sx se e2)
eesubst sx se (Case e1 e2 e3) = Case (eesubst sx se e1) (eesubst sx se e2) (eesubst sx se e3)
eesubst sx se (Fix e1) = Fix (eesubst sx se e1)
eesubst sx se (Let x e1 e2)
  | sx == x = Let x e1 e2
  | otherwise = Let x (eesubst sx se e1) (eesubst sx se e2)
eesubst sx se (LetRec x e1 e2)
  | sx == x = LetRec x e1 e2
  | otherwise = LetRec x (eesubst sx se e1) (eesubst sx se e2)
eesubst sx se (LetA x t e1 e2)
  | sx == x = LetA x t e1 e2
  | otherwise = LetA x t (eesubst sx se e1) (eesubst sx se e2)
eesubst _ _ RcdNil = RcdNil
eesubst sx se (RcdCons l1 e1 e2) = RcdCons l1 (eesubst sx se e1) (eesubst sx se e2)
eesubst sx se (RcdProj e1 l1) = RcdProj (eesubst sx se e1) l1

ttsubst :: String -> Typ -> Typ -> Typ
ttsubst _ _ TUnit = TUnit
ttsubst _ _ TInt = TInt
ttsubst _ _ TBool = TBool
ttsubst _ _ TTop = TTop
ttsubst _ _ TBot = TBot
ttsubst sa st (TVar a)
  | sa == a = st
  | otherwise = TVar a
ttsubst sa st (TAll a t)
  | sa == a = TAll a t
  | otherwise = TAll a (ttsubst sa st t)
ttsubst sa st (TArr t1 t2) =
  TArr (ttsubst sa st t1) (ttsubst sa st t2)
ttsubst sa st (TList t) = TList (ttsubst sa st t)
ttsubst sa st (TIntersection t1 t2) =
  TIntersection (ttsubst sa st t1) (ttsubst sa st t2)
ttsubst sa st (TUnion t1 t2) =
  TUnion (ttsubst sa st t1) (ttsubst sa st t2)
ttsubst _ _ (TLabel l) = TLabel l

etsubst :: String -> Typ -> Exp -> Exp
etsubst _ _ (ILit n) = ILit n
etsubst _ _ (BLit n) = BLit n
etsubst _ _ (Var x) = Var x
etsubst sa st (Lam x b) = Lam x (etsubst sa st b)
etsubst sa st (App e1 e2) = App (etsubst sa st e1) (etsubst sa st e2)
etsubst sa st (Ann e1 t) = Ann (etsubst sa st e1) (ttsubst sa st t)
etsubst sa st (TApp e1 t) = TApp (etsubst sa st e1) (ttsubst sa st t)
etsubst sa st (TAbs x e1) = TAbs x (etsubst sa st e1)
etsubst _ _ Nil = Nil
etsubst sa st (Cons e1 e2) = Cons (etsubst sa st e1) (etsubst sa st e2)
etsubst sa st (Case e1 e2 e3) = Case (etsubst sa st e1) (etsubst sa st e2) (etsubst sa st e3)
etsubst sa st (Fix e1) = Fix (etsubst sa st e1)
etsubst sa st (Let x e1 e2) = Let x (etsubst sa st e1) (etsubst sa st e2)
etsubst sa st (LetRec x e1 e2) = LetRec x (etsubst sa st e1) (etsubst sa st e2)
etsubst sa st (LetA x t e1 e2) = LetA x (ttsubst sa st t) (etsubst sa st e1) (etsubst sa st e2)
etsubst _ _ RcdNil = RcdNil
etsubst sa st (RcdCons l1 e1 e2) = RcdCons l1 (etsubst sa st e1) (etsubst sa st e2)
etsubst sa st (RcdProj e1 l1) = RcdProj (etsubst sa st e1) l1

ctsubst :: String -> Typ -> Judgment -> Judgment
ctsubst sa st (Sub t1 t2) = Sub (ttsubst sa st t1) (ttsubst sa st t2)
ctsubst sa st (Chk e a) = Chk (etsubst sa st e) (ttsubst sa st a)
ctsubst sa st (Inf e a f)
  | sa == a = Inf e a f
  | otherwise = Inf (etsubst sa st e) a (ctsubst sa st f)
ctsubst sa st (InfAbs t1 a b f)
  | sa == a || sa == b = InfAbs t1 a b f
  | otherwise = InfAbs (ttsubst sa st t1) a b (ctsubst sa st f)
ctsubst sa st (InfApp t1 t2 e a f)
  | sa == a = InfApp t1 t2 e a f
  | otherwise = InfApp (ttsubst sa st t1) (ttsubst sa st t2) (etsubst sa st e) a (ctsubst sa st f)
ctsubst sa st (InfProj t1 t2 t3 a f)
  | sa == a = InfProj t1 t2 t3 a f
  | otherwise = InfProj (ttsubst sa st t1) (ttsubst sa st t2) (ttsubst sa st t3) a (ctsubst sa st f)
ctsubst sa st (InfTApp t1 t2 a f)
  | sa == a = InfTApp t1 t2 a f
  | otherwise = InfTApp (ttsubst sa st t1) (ttsubst sa st t2) a (ctsubst sa st f)
ctsubst sa st (CaseChk e a b) = CaseChk (etsubst sa st e) (ttsubst sa st a) (ttsubst sa st b)
ctsubst sa st (CaseInf t1 e e1 a f) = CaseInf (ttsubst sa st t1) (etsubst sa st e) (etsubst sa st e1) a (ctsubst sa st f)
ctsubst sa st (ConsInf t1 e a f) = ConsInf (ttsubst sa st t1) (etsubst sa st e) a (ctsubst sa st f)
ctsubst sa st (LetInf x t e a f) = LetInf x (ttsubst sa st t) (etsubst sa st e) a (ctsubst sa st f)
ctsubst _ _ End = End

ftvarInTyp :: Typ -> [String]
ftvarInTyp TUnit = []
ftvarInTyp TInt = []
ftvarInTyp TBool = []
ftvarInTyp TTop = []
ftvarInTyp TBot = []
ftvarInTyp (TVar a) = [a]
ftvarInTyp (TAll a c) = delete a (ftvarInTyp c)
ftvarInTyp (TArr t1 t2) = ftvarInTyp t1 `union` ftvarInTyp t2
ftvarInTyp (TList t1) = ftvarInTyp t1
ftvarInTyp (TIntersection t1 t2) = ftvarInTyp t1 `union` ftvarInTyp t2
ftvarInTyp (TUnion t1 t2) = ftvarInTyp t1 `union` ftvarInTyp t2
ftvarInTyp (TLabel _) = []

tvarInTyp :: Typ -> [String]
tvarInTyp TUnit = []
tvarInTyp TInt = []
tvarInTyp TBool = []
tvarInTyp TTop = []
tvarInTyp TBot = []
tvarInTyp (TVar a) = [a]
tvarInTyp (TAll a t) = [a] `union` tvarInTyp t
tvarInTyp (TArr t1 t2) = tvarInTyp t1 `union` tvarInTyp t2
tvarInTyp (TList t1) = tvarInTyp t1
tvarInTyp (TIntersection t1 t2) = tvarInTyp t1 `union` tvarInTyp t2
tvarInTyp (TUnion t1 t2) = tvarInTyp t1 `union` tvarInTyp t2
tvarInTyp (TLabel _) = []

tvarInExp :: Exp -> [String]
tvarInExp (Var _) = []
tvarInExp (ILit _) = []
tvarInExp (BLit _) = []
tvarInExp (Lam _ b) = tvarInExp b
tvarInExp (App e1 e2) = tvarInExp e1 `union` tvarInExp e2
tvarInExp (Ann e t) = tvarInTyp t `union` tvarInExp e
tvarInExp (TApp e t) = tvarInTyp t `union` tvarInExp e
tvarInExp (TAbs x e) = [x] `union` tvarInExp e
tvarInExp Nil = []
tvarInExp (Cons e1 e2) = tvarInExp e1 `union` tvarInExp e2
tvarInExp (Case e1 e2 e3) = tvarInExp e1 `union` tvarInExp e2 `union` tvarInExp e3
tvarInExp (Fix e) = tvarInExp e
tvarInExp (Let _ e1 e2) = tvarInExp e1 `union` tvarInExp e2
tvarInExp (LetRec _ e1 e2) = tvarInExp e1 `union` tvarInExp e2
tvarInExp (LetA _ t e1 e2) = tvarInTyp t `union` tvarInExp e1 `union` tvarInExp e2
tvarInExp RcdNil = []
tvarInExp (RcdCons _ e1 e2) = tvarInExp e1 `union` tvarInExp e2
tvarInExp (RcdProj e _) = tvarInExp e

tvarInJug :: Judgment -> [String]
tvarInJug (Sub t1 t2) = tvarInTyp t1 `union` tvarInTyp t2
tvarInJug (Chk e t) = tvarInExp e `union` tvarInTyp t
tvarInJug (Inf e a f) = tvarInExp e `union` tvarInJug f `union` [a]
tvarInJug (InfAbs t a b f) = tvarInTyp t `union` tvarInJug f `union` [a, b]
tvarInJug (InfApp t1 t2 e a c) = tvarInExp e `union` tvarInTyp t1 `union` tvarInTyp t2 `union` tvarInJug c `union` [a]
tvarInJug (InfProj t1 t2 t3 a c) = tvarInTyp t1 `union` tvarInTyp t2 `union` tvarInTyp t3 `union` tvarInJug c `union` [a]
tvarInJug (InfTApp t1 t2 a f) = tvarInTyp t1 `union` tvarInTyp t2 `union` tvarInJug f `union` [a]
tvarInJug (CaseChk e t1 t2) = tvarInExp e `union` tvarInTyp t1 `union` tvarInTyp t2
tvarInJug (CaseInf t e1 e2 a f) = tvarInTyp t `union` tvarInExp e1 `union` tvarInExp e2 `union` tvarInJug f `union` [a]
tvarInJug (ConsInf t e a f) = tvarInTyp t `union` tvarInExp e `union` tvarInJug f `union` [a]
tvarInJug (LetInf _ t e a f) = tvarInTyp t `union` tvarInExp e `union` tvarInJug f `union` [a]
tvarInJug End = []

findVar :: String -> Worklist -> Maybe Typ
findVar x (WVar y a : w)
  | x == y = Just a
  | otherwise = findVar x w
findVar x (_ : w) = findVar x w
findVar _ [] = Nothing

tvarInTyps :: [Typ] -> [String]
tvarInTyps = foldl union [] . map tvarInTyp

pickNewTVar :: [Work] -> [String] -> [Char]
pickNewTVar ws as = genFreshTVar (wtvars `union` as)
  where
    wtvars =
      concatMap
        ( \case
            WTVar a _ -> [a]
            WVar _ t -> tvarInTyp t
            WJug c -> tvarInJug c
        )
        ws

varInExp :: Exp -> [String]
varInExp (Var x) = [x]
varInExp (ILit _) = []
varInExp (BLit _) = []
varInExp (Lam x b) = x : varInExp b
varInExp (App e1 e2) = varInExp e1 `union` varInExp e2
varInExp (Ann e _) = varInExp e
varInExp (TApp e _) = varInExp e
varInExp (TAbs _ e) = varInExp e
varInExp Nil = []
varInExp (Cons e1 e2) = varInExp e1 `union` varInExp e2
varInExp (Case e1 e2 e3) = varInExp e1 `union` varInExp e2 `union` varInExp e3
varInExp (Fix e) = varInExp e
varInExp (Let _ e1 e2) = varInExp e1 `union` varInExp e2
varInExp (LetRec x e1 e2) = x : varInExp e1 ++ varInExp e2
varInExp (LetA x _ e1 e2) = x : varInExp e1 ++ varInExp e2
varInExp RcdNil = []
varInExp (RcdCons _ e1 e2) = varInExp e1 ++ varInExp e2
varInExp (RcdProj e _) = varInExp e

varInJug :: Judgment -> [String]
varInJug (Sub _ _) = []
varInJug (Chk e _) = varInExp e
varInJug (Inf e _ f) = varInExp e `union` varInJug f
varInJug (InfAbs _ _ _ f) = varInJug f
varInJug (InfApp _ _ e _ f) = varInExp e `union` varInJug f
varInJug (InfProj _ _ _ _ f) = varInJug f
varInJug (InfTApp _ _ _ f) = varInJug f
varInJug (CaseChk e _ _) = varInExp e
varInJug (CaseInf _ e1 e2 _ f) = varInExp e1 `union` varInExp e2 `union` varInJug f
varInJug (ConsInf _ e _ f) = varInExp e `union` varInJug f
varInJug (LetInf x _ e _ f) = varInExp e `union` varInJug f `union` [x]
varInJug End = []

varInExps :: [Exp] -> [String]
varInExps = foldl union [] . map varInExp

pickNewVar :: [Work] -> [String] -> String
pickNewVar ws xs = genFreshVar (wvars `union` xs)
  where
    wvars =
      concatMap
        ( \case
            WVar a _ -> [a]
            WJug c -> varInJug c
            _ -> []
        )
        ws

findTVar :: [Work] -> String -> TBind
findTVar w a = head [t | WTVar a' t <- w, a == a']

mono :: [Work] -> Typ -> Bool
mono _ TUnit = True
mono _ TInt = True
mono _ TBool = True
mono _ TTop = False
mono _ TBot = False
mono w (TVar a) = findTVar w a == TVarBind || findTVar w a == ETVarBind
mono _ (TIntersection _ _) = False
mono _ (TUnion _ _) = False
mono _ (TAll {}) = False
mono w (TArr a b) = mono w a && mono w b
mono w (TList t) = mono w t
mono _ (TLabel _) = True

monoIU :: [Work] -> Typ -> Bool
monoIU _ TUnit = True
monoIU _ TInt = True
monoIU _ TBool = True
monoIU _ TTop = False
monoIU _ TBot = False
monoIU w (TVar a) = findTVar w a == TVarBind || findTVar w a == ETVarBind
monoIU w (TIntersection a b) = monoIU w a && monoIU w b
monoIU w (TUnion a b) = monoIU w a && monoIU w b
monoIU _ (TAll {}) = False
monoIU w (TArr a b) = monoIU w a && monoIU w b
monoIU w (TList t) = monoIU w t
monoIU _ (TLabel _) = True

notAll :: [Work] -> Typ -> Bool
notAll _ TUnit = True
notAll _ TInt = True
notAll _ TBool = True
notAll _ TTop = True
notAll _ TBot = False
notAll w (TVar a) = findTVar w a == TVarBind || findTVar w a == ETVarBind
notAll w (TIntersection a b) = notAll w a && notAll w b
notAll w (TUnion a b) = notAll w a || notAll w b
notAll _ (TAll {}) = False
notAll _ (TArr _ _) = True
notAll _ (TList _) = True
notAll _ (TLabel _) = True

insertETVar :: String -> String -> Worklist -> Worklist
insertETVar a b (WTVar c ETVarBind : w)
  | a == c = WTVar a ETVarBind : WTVar b ETVarBind : w
  | otherwise = WTVar c ETVarBind : insertETVar a b w
insertETVar a b (x : w) = x : insertETVar a b w
insertETVar _ _ _ = error "insert error"

substWL :: String -> Typ -> Worklist -> Worklist
substWL a t (WTVar b ETVarBind : w)
  | a == b = w
  | b `notElem` ftvarInTyp t = WTVar b ETVarBind : substWL a t w
  | otherwise = substWL a t (insertETVar a b w)
substWL a t (WTVar b TVarBind : w)
  | b `notElem` ftvarInTyp t = WTVar b TVarBind : substWL a t w
  | otherwise = error $ b ++ " ∈ FV(" ++ show t ++ ")."
substWL a t (WTVar b STVarBind : w)
  | b `notElem` ftvarInTyp t = WTVar b STVarBind : substWL a t w
  | otherwise = error $ show b ++ " ∈ FV(" ++ show t ++ ")."
substWL a t (WVar x t1 : w) = WVar x (ttsubst a t t1) : substWL a t w
substWL a t (WJug c : w) = WJug (ctsubst a t c) : substWL a t w
substWL a t w = error $ "substWL {" ++ show t ++ " / ^" ++ a ++ "} (" ++ show w ++ ") fails."

notIntersection :: Typ -> Bool
notIntersection (TIntersection _ _) = False
notIntersection _ = True

notUnion :: Typ -> Bool
notUnion (TUnion _ _) = False
notUnion _ = True

curInfo :: Int -> [Work] -> String -> String
curInfo n ws s1 = show ws ++ "\n" ++ replicate n ' ' ++ "-->{ Rule: " ++ s1 ++ replicate (15 - length s1) ' ' ++ " }\n"

baseRules :: [String]
baseRules =
  [ "GCTVar",
    "GCVar",
    "≤⊤",
    "≤⊥",
    "≤Unit",
    "≤Int",
    "≤Bool",
    "≤TVar",
    "≤→",
    "≤∀",
    "≤∀L",
    "≤MonoL",
    "≤MonoR",
    "≤SplitL",
    "≤SplitR",
    "≤∩R",
    "≤∩L",
    "≤∪L",
    "≤∪R",
    "⇐λ",
    "⇐λ⊤",
    "⇐λα",
    "⇐∩",
    "⇐∪",
    "⇐Sub",
    "⇒Var",
    "⇒Int",
    "⇒Bool",
    "⇒Anno",
    "⇒ΛAnno",
    "⇒App",
    "⇒TApp",
    "⇒→Mono",
    "▹→",
    "▹⊥",
    "▹∀",
    "▹∩",
    "▹∪",
    "▹α",
    "⊙➤",
    "∘∀",
    "∘⊥",
    "∘∩",
    "∘∪"
  ]

rcdRules :: [String]
rcdRules =
  [ "≤Label",
    "⇒⟨⟩",
    "⇒⟨⟩Cons",
    "⇒Proj",
    "⊗➤"
  ]

extRules :: [String]
extRules =
  [ "≤[]",
    "≤[]αL",
    "≤[]αR",
    "⇐[]Ni",
    "⇐[]Cons",
    "⇐Case",
    "⇐Fix",
    "⇐LetA",
    "Case⇐",
    "⇒Λ",
    "⇒[]Nil",
    "⇒[]Cons",
    "⇒[]Case",
    "[]Cons⇒",
    "[]Case⇒",
    "⇒Fix",
    "⇒Let",
    "⇒LetRec",
    "⇒LetA"
  ]

-- useRule :: String -> Bool
-- useRule rName = rName `elem` baseRules

useRule :: String -> Bool
useRule _ = True

bigStep :: Bool -> Int -> Int -> String -> [Work] -> (Bool, String)
bigStep _ n m info _ | n > m = (False, info)
bigStep _ _ _ info [] = (True, info)
bigStep mFlag n m info ws@(WTVar _ _ : w)
  | useRule "GCTVar" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "GCTVar") w
bigStep mFlag n m info ws@(WVar _ _ : w)
  | useRule "GCVar" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "GCVar") w
--
-- Subtyping
--
bigStep mFlag n m info ws@(WJug (Sub _ TTop) : w)
  | useRule "≤⊤" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤⊤") w
bigStep mFlag n m info ws@(WJug (Sub TBot _) : w)
  | useRule "≤⊥" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤⊥") w
bigStep mFlag n m info ws@(WJug (Sub TUnit TUnit) : w)
  | useRule "≤Unit" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤Unit") w
bigStep mFlag n m info ws@(WJug (Sub TInt TInt) : w)
  | useRule "≤Int" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤Int") w
bigStep mFlag n m info ws@(WJug (Sub TBool TBool) : w)
  | useRule "≤Bool" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤Bool") w
bigStep mFlag n m info ws@(WJug (Sub (TVar a) (TVar b)) : w)
  | useRule "≤TVar" && a == b = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤TVar") w
bigStep mFlag n m info ws@(WJug (Sub (TArr t1 t2) (TArr t3 t4)) : w)
  | useRule "≤→" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤→") ws'
  where
    ws' = WJug (Sub t2 t4) : WJug (Sub t3 t1) : w
bigStep mFlag n m info ws@(WJug (Sub (TAll a t1) (TAll b t2)) : w)
  | useRule "≤∀" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤∀") ws'
  where
    c = pickNewTVar ws []
    t1' = ttsubst a (TVar c) t1
    t2' = ttsubst b (TVar c) t2
    ws' = WJug (Sub t1' t2') : WTVar c STVarBind : w
bigStep mFlag n m info ws@(WJug (Sub (TAll a t1) t2) : w)
  | useRule "≤∀L" && notAll w t2 = case t2 of
      TIntersection t21 t22 -> case bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤∩R") (WJug (Sub (TAll a t1) t21) : WJug (Sub (TAll a t1) t22) : w) of
        (True, info') -> (True, info')
        (False, info') -> bigStep mFlag (n + 1) m (info' ++ replicate n ' ' ++ curInfo n ws "≤∀L") ws'
      TUnion t21 t22 -> case bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤∀L") ws' of
        (True, info') -> (True, info')
        (False, info') -> case bigStep mFlag (n + 1) m (info' ++ replicate n ' ' ++ curInfo n ws "≤∪R1") (WJug (Sub (TAll a t1) t21) : w) of
          (True, info'') -> (True, info'')
          (False, info'') -> bigStep mFlag (n + 1) m (info'' ++ replicate n ' ' ++ curInfo n ws "≤∪R2") (WJug (Sub (TAll a t1) t22) : w)
      _ -> bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤∀L") ws'
  where
    b = pickNewTVar ws []
    t1' = ttsubst a (TVar b) t1
    ws' = WJug (Sub t1' t2) : WTVar b ETVarBind : w
bigStep mFlag n m info ws@(WJug (Sub (TVar a) t) : w)
  | commonCond && mFlag && monoIU w t = case monoLResult of
      (True, info') -> (True, info')
      (False, info') -> case t of
        TUnion t1 t2 -> case bigStep mFlag (n + 1) m (info' ++ replicate n ' ' ++ curInfo n ws "≤∪L1") (WJug (Sub (TVar a) t1) : w) of
          (True, info'') -> (True, info'')
          (False, info'') -> bigStep mFlag (n + 1) m (info'' ++ replicate n ' ' ++ curInfo n ws "≤∪L2") (WJug (Sub (TVar a) t2) : w)
        _ -> (False, info')
  | commonCond && not mFlag && mono w t = monoLResult
  where
    ws' = substWL a t w
    commonCond = useRule "≤MonoL" && findTVar w a == ETVarBind && (a `notElem` ftvarInTyp t)
    monoLResult = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤MonoL") ws'
bigStep mFlag n m info ws@(WJug (Sub t (TVar a)) : w)
  | commonCond && mFlag && monoIU w t = case monoRResult of
      (True, info') -> (True, info')
      (False, info') -> case t of
        TIntersection t1 t2 -> case bigStep mFlag (n + 1) m (info' ++ replicate n ' ' ++ curInfo n ws "≤∩R") (WJug (Sub t1 (TVar a)) : WJug (Sub t2 (TVar a)) : w) of
          (True, info'') -> (True, info'')
          (False, info'') -> bigStep mFlag (n + 1) m (info'' ++ replicate n ' ' ++ curInfo n ws "≤∩L") (WJug (Sub t1 (TVar a)) : w)
        _ -> (False, info')
  | commonCond && not mFlag && mono w t = monoRResult
  where
    ws' = substWL a t w
    commonCond = useRule "≤MonoR" && findTVar w a == ETVarBind && (a `notElem` ftvarInTyp t)
    monoRResult = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤MonoR") ws'
bigStep mFlag n m info ws@(WJug (Sub (TVar a) (TArr t1 t2)) : w)
  | useRule "≤SplitL" && not (mono w (TArr t1 t2)) && findTVar w a == ETVarBind = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤SplitL") ws'
  where
    a1 = pickNewTVar w []
    a2 = pickNewTVar w [a1]
    ws' = WJug (Sub (TArr (TVar a1) (TVar a2)) (TArr t1 t2)) : substWL a (TArr (TVar a1) (TVar a2)) (WTVar a2 ETVarBind : WTVar a1 ETVarBind : w)
bigStep mFlag n m info ws@(WJug (Sub (TArr t1 t2) (TVar a)) : w)
  | useRule "≤SplitR" && not (mono w (TArr t1 t2)) && findTVar w a == ETVarBind = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤SplitR") ws'
  where
    a1 = pickNewTVar w []
    a2 = pickNewTVar w [a1]
    ws' = WJug (Sub (TArr (TVar a1) (TVar a2)) (TArr t1 t2)) : substWL a (TArr (TVar a1) (TVar a2)) (WTVar a2 ETVarBind : WTVar a1 ETVarBind : w)
bigStep mFlag n m info ws@(WJug (Sub t1 (TIntersection t2 t3)) : w)
  | useRule "≤∩R" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤∩R") ws'
  where
    ws' = WJug (Sub t1 t3) : WJug (Sub t1 t2) : w
bigStep mFlag n m info ws@(WJug (Sub (TIntersection t11 t12) t2) : w)
  | useRule "≤∩L" = case bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤∩L1") (WJug (Sub t11 t2) : w) of
      (True, info') -> (True, info')
      (False, info') -> bigStep mFlag (n + 1) m (info' ++ replicate n ' ' ++ curInfo n ws "≤∩L2") (WJug (Sub t12 t2) : w)
bigStep mFlag n m info ws@(WJug (Sub (TUnion t11 t12) t2) : w)
  | useRule "≤∪L" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤∪L") ws'
  where
    ws' = WJug (Sub t11 t2) : WJug (Sub t12 t2) : w
bigStep mFlag n m info ws@(WJug (Sub t1 (TUnion t21 t22)) : w)
  | useRule "≤∪R" = case bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤∪R1") (WJug (Sub t1 t21) : w) of
      (True, info') -> (True, info')
      (False, info') -> bigStep mFlag (n + 1) m (info' ++ replicate n ' ' ++ curInfo n ws "≤∪R2") (WJug (Sub t1 t22) : w)
bigStep mFlag n m info ws@(WJug (Sub (TLabel l1) (TLabel l2)) : w) -- Record Extension
  | useRule "≤Label" && l1 == l2 = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤Label") w
bigStep mFlag n m info ws@(WJug (Sub (TList a) (TList b)) : w)
  | useRule "≤[]" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤[]") ws' -- Unformalized
  where
    ws' = WJug (Sub a b) : w
bigStep mFlag n m info ws@(WJug (Sub (TVar a) (TList t)) : w) -- Unformalized
  | useRule "≤[]αL" && findTVar w a == ETVarBind = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤[]αL") ws'
  where
    b = pickNewTVar (WJug (Sub (TVar a) (TList t)) : w) []
    ws' = WJug (Sub (TVar b) t) : substWL a (TList (TVar b)) (WTVar b ETVarBind : w)
bigStep mFlag n m info ws@(WJug (Sub (TVar a) (TList t)) : w) -- Unformalized
  | useRule "≤[]αR" && findTVar w a == ETVarBind = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "≤[]αR") ws'
  where
    b = pickNewTVar (WJug (Sub (TVar a) (TList t)) : w) []
    ws' = WJug (Sub (TVar b) t) : substWL a (TList (TVar b)) (WTVar b ETVarBind : w)
--
-- Checking
--
bigStep mFlag n m info ws@(WJug (Chk (Lam x e) (TArr t1 t2)) : w)
  | useRule "⇐λ" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐λ") ws'
  where
    y = pickNewVar (WJug (Chk (Lam x e) (TArr t1 t2)) : w) []
    e' = eesubst x (Var y) e
    ws' = WJug (Chk e' t2) : WVar y t1 : w
bigStep mFlag n m info ws@(WJug (Chk (Lam x e) TTop) : w)
  | useRule "⇐λ⊤" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐λ⊤") ws'
  where
    y = pickNewVar (WJug (Chk (Lam x e) TTop) : w) []
    e' = eesubst x (Var y) e
    ws' = WJug (Chk e' TTop) : WVar y TBot : w
bigStep mFlag n m info ws@(WJug (Chk (Lam x e) (TVar a)) : w)
  | useRule "⇐λα" && findTVar ws a == ETVarBind = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐λα") ws'
  where
    a1 = pickNewTVar ws []
    a2 = pickNewTVar ws [a1]
    y = pickNewVar ws []
    e' = eesubst x (Var y) e
    ws' = WJug (Chk e' (TVar a2)) : WVar y (TVar a1) : substWL a (TArr (TVar a1) (TVar a2)) (WTVar a2 ETVarBind : WTVar a1 ETVarBind : w)
bigStep mFlag n m info ws@(WJug (Chk e (TIntersection t1 t2)) : w)
  | useRule "⇐∩" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐∩") ws'
  where
    ws' = WJug (Chk e t2) : WJug (Chk e t1) : w
bigStep mFlag n m info ws@(WJug (Chk e (TUnion t1 t2)) : w)
  | useRule "⇐∪" = case bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐∪1") (WJug (Chk e t1) : w) of
      (True, info') -> (True, info')
      (False, info') -> bigStep mFlag (n + 1) m (info' ++ replicate n ' ' ++ curInfo n ws "⇐∪2") (WJug (Chk e t2) : w)
bigStep mFlag n m info ws@(WJug (Chk Nil (TList _)) : w) -- Unformalized
  | useRule "⇐[]Nil" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐[]Nil") w
bigStep mFlag n m info ws@(WJug (Chk (Cons e1 e2) (TList a)) : w) -- Unformalized
  | useRule "⇐[]Cons" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐[]Cons") ws'
  where
    ws' = WJug (Chk e1 a) : WJug (Chk e2 (TList a)) : w
bigStep mFlag n m info ws@(WJug (Chk (Case e e1 e2) t1) : w) -- Unformalized
  | useRule "⇐Case" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐Case") ws'
  where
    a = pickNewTVar ws []
    ws' = WJug (Chk e1 t1) : WJug (Inf e a (CaseChk e2 (TVar a) t1)) : w
bigStep mFlag n m info ws@(WJug (Chk (Fix e) t) : w) -- Unformalized
  | useRule "⇐Fix" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐Fix") ws'
  where
    ws' = WJug (Chk e (TArr t t)) : w
bigStep mFlag n m info ws@(WJug (Chk (LetA x t1 e1 e2) t2) : w) -- Unformalized
  | useRule "⇐LetA" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐LetA") ws'
  where
    ws' = WJug (Chk (App (Ann (Lam x e2) (TArr t1 t2)) (Ann (Fix (Lam x e1)) t1)) t2) : w
-- assumes non-overlapping with ⇔∩, ⇔∪
bigStep mFlag n m info ws@(WJug (Chk e t) : w)
  | useRule "⇐Sub" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇐Sub") ws'
  where
    b = pickNewTVar ws []
    ws' = WJug (Inf e b (Sub (TVar b) t)) : w
bigStep mFlag n m info ws@(WJug (CaseChk e (TList t1) t2) : w)
  | useRule "Case⇐" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "Case⇐") ws' -- Unformalized
  where
    ws' = WJug (Chk e (TArr t1 (TArr (TList t1) t2))) : w
--
-- Inference
--
bigStep mFlag n m info ws@(WJug (Inf (Var x) b c) : w)
  | useRule "⇒Var" =
      case findVar x w of
        Just t -> bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒Var") ws'
          where
            ws' = WJug (ctsubst b t c) : w
        Nothing -> (False, info)
bigStep mFlag n m info ws@(WJug (Inf (ILit _) b c) : w)
  | useRule "⇒Int" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒Int") ws'
  where
    ws' = WJug (ctsubst b TInt c) : w
bigStep mFlag n m info ws@(WJug (Inf (BLit _) b c) : w)
  | useRule "⇒Bool" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒Bool") ws'
  where
    ws' = WJug (ctsubst b TBool c) : w
bigStep mFlag n m info ws@(WJug (Inf (Ann e t) b c) : w)
  | useRule "⇒Anno" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒Anno") ws'
  where
    ws' = WJug (Chk e t) : WJug (ctsubst b t c) : w
bigStep mFlag n m info ws@(WJug (Inf (TAbs a (Ann e t)) b c) : w)
  | useRule "⇒ΛAnno" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒ΛAnno") ws'
  where
    a1 = pickNewTVar ws []
    e' = etsubst a (TVar a1) e
    t' = ttsubst a (TVar a1) t
    ws' = WJug (Chk e' t') : WTVar a1 TVarBind : WJug (ctsubst b (TAll a1 t') c) : w
-- \*** new rules
bigStep mFlag n m info ws@(WJug (Inf (TAbs a e) b c) : w)
  | useRule "⇒Λ" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒Λ") ws'
  where
    -- \*** also tvars in e
    a1 = pickNewTVar ws []
    b1 = pickNewTVar ws [a1]
    e' = etsubst a (TVar a1) e
    -- have to exploit the name clash here
    -- some scoping issue here, but should not cause problem in the impl
    ws' = WJug (Inf e' b1 (ctsubst b (TAll a1 (TVar b1)) c)) : WTVar a1 TVarBind : w
bigStep mFlag n m info ws@(WJug (Inf (App e1 e2) a c) : w)
  | useRule "⇒App" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒App") ws'
  where
    a1 = pickNewTVar ws []
    a2 = pickNewTVar ws [a1]
    a3 = pickNewTVar ws [a1, a2]
    ws' = WJug (Inf e1 a1 (InfAbs (TVar a1) a2 a3 (InfApp (TVar a2) (TVar a3) e2 a c))) : w
bigStep mFlag n m info ws@(WJug (Inf (TApp e t1) b c) : w)
  | useRule "⇒TApp" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒TApp") ws'
  where
    b1 = pickNewTVar ws []
    ws' = WJug (Inf e b1 (InfTApp (TVar b1) t1 b c)) : w
bigStep mFlag n m info ws@(WJug (Inf (Lam x e) b c) : w)
  | useRule "⇒→Mono" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒→Mono") ws'
  where
    a1 = pickNewTVar ws []
    a2 = pickNewTVar ws [a1]
    y = pickNewVar ws []
    e' = eesubst x (Var y) e
    ws' = WJug (Chk e' (TVar a2)) : WVar y (TVar a1) : WJug (ctsubst b (TArr (TVar a1) (TVar a2)) c) : WTVar a2 ETVarBind : WTVar a1 ETVarBind : w
bigStep mFlag n m info ws@(WJug (Inf RcdNil b c) : w)
  | useRule "⇒⟨⟩" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒⟨⟩") ws' -- Record Extension
  where
    ws' = WJug (ctsubst b TUnit c) : w
bigStep mFlag n m info ws@(WJug (Inf (RcdCons l1 e1 e2) b c) : w)
  | useRule "⇒⟨⟩Cons" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒⟨⟩Cons") ws' -- Record Extension
  where
    b1 = pickNewTVar ws []
    b2 = pickNewTVar ws [b1]
    ws' = WJug (Inf e1 b1 (Inf e2 b2 (ctsubst b ((TLabel l1 `TArr` TVar b1) `TIntersection` TVar b2) c))) : w
bigStep mFlag n m info ws@(WJug (Inf (RcdProj e l) b c) : w)
  | useRule "⇒Proj" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒Proj") ws' -- Record Extension
  where
    b1 = pickNewTVar ws []
    b2 = pickNewTVar ws [b1]
    b3 = pickNewTVar ws [b1, b2]
    ws' = WJug (Inf e b1 (InfAbs (TVar b1) b2 b3 (InfProj (TVar b2) (TVar b3) (TLabel l) b c))) : w
bigStep mFlag n m info ws@(WJug (Inf Nil b c) : w)
  | useRule "⇒[]Nil" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒[]Nil") ws' -- Unformalized
  where
    a = pickNewTVar w []
    ws' = WJug (ctsubst b (TList (TVar a)) c) : WTVar a ETVarBind : w
bigStep mFlag n m info ws@(WJug (Inf (Cons e1 e2) b c) : w)
  | useRule "⇒[]Cons" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒[]Cons") ws' -- Unformalized
  where
    b1 = pickNewTVar ws []
    ws' = WJug (Inf e1 b1 (ConsInf (TVar b1) e2 b c)) : w
bigStep mFlag n m info ws@(WJug (Inf (Case e e1 e2) b c) : w)
  | useRule "⇒[]Case" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒[]Case") ws' -- Unformalized
  where
    b1 = pickNewTVar ws []
    ws' = WJug (Inf e1 b1 (CaseInf (TVar b1) e e2 b c)) : w
bigStep mFlag n m info ws@(WJug (ConsInf t e b c) : w)
  | useRule "[]Cons⇒" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "[]Cons⇒") ws' -- Unformalized
  where
    ws' = WJug (Chk e (TList t)) : WJug (ctsubst b t c) : w
bigStep mFlag n m info ws@(WJug (CaseInf t1 e1 e2 b c) : w)
  | useRule "[]Case⇒" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "[]Case⇒") ws' -- Unformalized
  where
    b1 = pickNewTVar ws []
    ws' = WJug (Inf e1 b1 (CaseChk e2 (TVar b1) t1)) : WJug (ctsubst b t1 c) : w
bigStep mFlag n m info ws@(WJug (Inf (Fix e) b c) : w)
  | useRule "⇒Fix" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒Fix") ws' -- Unformalized
  where
    a = pickNewTVar ws []
    ws' = WJug (Chk e (TArr (TVar a) (TVar a))) : WJug (ctsubst b (TVar a) c) : WTVar a ETVarBind : w
bigStep mFlag n m info ws@(WJug (Inf (Let x e1 e2) b c) : w)
  | useRule "⇒Let" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒Let") ws' -- Unformalized
  where
    a = pickNewTVar ws []
    ws' = WJug (Inf e1 a (LetInf x (TVar a) e2 b c)) : w
bigStep mFlag n m info ws@(WJug (LetInf x t e b c) : w)
  | useRule "Let⇒" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "Let⇒") ws' -- Unformalized
  where
    ws' = WJug (Inf e b c) : WVar x t : w
bigStep mFlag n m info ws@(WJug (Inf (LetRec x e1 e2) b c) : w)
  | useRule "⇒LetRec" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒LetRec") ws' -- Unformalized
  where
    ws' = WJug (Inf (App (Lam x e2) (Fix (Lam x e1))) b c) : w
bigStep mFlag n m info ws@(WJug (Inf (LetA x t e1 e2) b c) : w)
  | useRule "⇒LetA" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⇒LetA") ws' -- Unformalized
  where
    ws' = WJug (Inf e2 b c) : WJug (Chk e1 t) : WVar x t : w
--
-- Matching and Application Inference
--
bigStep mFlag n m info ws@(WJug (InfAbs (TArr t1 t2) b1 b2 c) : w)
  | useRule "▹→" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "▹→") ws'
  where
    ws' = WJug (ctsubst b2 t2 (ctsubst b1 t1 c)) : w
bigStep mFlag n m info ws@(WJug (InfAbs TBot b1 b2 c) : w)
  | useRule "▹⊥" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "▹⊥") ws'
  where
    ws' = WJug (ctsubst b2 TBot (ctsubst b1 TTop c)) : w
bigStep mFlag n m info ws@(WJug (InfAbs (TAll a t) b1 b2 c) : w)
  | useRule "▹∀" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "▹∀") ws'
  where
    a1 = pickNewTVar ws []
    t' = ttsubst a (TVar a1) t
    ws' = WJug (InfAbs t' b1 b2 c) : WTVar a1 ETVarBind : w
bigStep mFlag n m info ws@(WJug (InfAbs (TIntersection t1 t2) b1 b2 c) : w)
  | useRule "▹∩" = case bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "▹∩1") (WJug (InfAbs t1 b1 b2 c) : w) of
      (True, info') -> (True, info')
      (False, _) -> bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "▹∩2") (WJug (InfAbs t2 b1 b2 c) : w)
bigStep mFlag n m info ws@(WJug (InfAbs (TUnion t1 t2) b1 b2 c) : w)
  | useRule "▹∪" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "▹∪") ws'
  where
    b3 = pickNewTVar ws []
    b4 = pickNewTVar ws [b3]
    b5 = pickNewTVar ws [b3, b4]
    b6 = pickNewTVar ws [b3, b4, b5]
    ws' = WJug (InfAbs t1 b3 b4 (InfAbs t2 b5 b6 (ctsubst b1 (TIntersection (TVar b3) (TVar b5)) (ctsubst b2 (TUnion (TVar b4) (TVar b6)) c)))) : w
bigStep mFlag n m info ws@(WJug (InfAbs (TVar a) b1 b2 c) : w)
  | useRule "▹α" && findTVar w a == ETVarBind = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "▹α") ws'
  where
    a1 = pickNewTVar ws []
    a2 = pickNewTVar ws [a1]
    ws' = substWL a (TArr (TVar a1) (TVar a2)) (WJug (InfAbs (TVar a) b1 b2 c) : WTVar a2 ETVarBind : WTVar a1 ETVarBind : w)
bigStep mFlag n m info ws@(WJug (InfApp t1 t2 e b c) : w)
  | useRule "⊙➤" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⊙➤") ws'
  where
    ws' = WJug (Chk e t1) : WJug (ctsubst b t2 c) : w
bigStep mFlag n m info ws@(WJug (InfProj t1 t2 t3 b c) : w)
  | useRule "⊗➤" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "⊗➤") ws'
  where
    ws' = WJug (Sub t3 t1) : WJug (ctsubst b t2 c) : w
--
-- Type Application Inference
--
bigStep mFlag n m info ws@(WJug (InfTApp (TAll a t1) t2 b c) : w)
  | useRule "∘∀" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "∘∀") ws'
  where
    ws' = WJug (ctsubst b (ttsubst a t2 t1) c) : w
bigStep mFlag n m info ws@(WJug (InfTApp TBot _ b c) : w)
  | useRule "∘⊥" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "∘⊥") ws'
  where
    ws' = WJug (ctsubst b TBot c) : w
bigStep mFlag n m info ws@(WJug (InfTApp (TIntersection t1 t2) t3 b c) : w)
  | useRule "∘∩" = case bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "∘∩1") (WJug (InfTApp t1 t3 b c) : w) of
      (True, info') -> (True, info')
      (False, _) -> bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "∘∩1") (WJug (InfTApp t2 t3 b c) : w)
bigStep mFlag n m info ws@(WJug (InfTApp (TUnion t1 t2) t3 b c) : w)
  | useRule "∘∪" = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "∘∪") ws'
  where
    b1 = pickNewTVar ws []
    b2 = pickNewTVar ws [b1]
    ws' = WJug (InfTApp t1 t3 b1 (InfTApp t2 t3 b2 (ctsubst b (TUnion (TVar b1) (TVar b2)) c))) : w
--
-- Dummy
--
bigStep mFlag n m info ws@(WJug End : w) = bigStep mFlag (n + 1) m (info ++ replicate n ' ' ++ curInfo n ws "Dummy") w
--
-- Stuck
--
bigStep _ n _ info ws = (False, info ++ replicate n ' ' ++ curInfo n ws "Stuck")

run :: FilePath -> Bool -> IO ()
run s mFlag = do
  code <- readFile s
  case parseExp code of
    Left err -> putStrLn err
    Right e ->
      (if flag then putStrLn $ "Accepted! (" ++ mFlagMessage ++ ")\n" ++ message else putStrLn $ "Rejected! (" ++ mFlagMessage ++ ")\n" ++ message)
      where
        b = pickNewTVar [] (tvarInExp e)
        ws = [WJug (Inf e b End)]
        (flag, message) = bigStep mFlag 0 400 "" ws
        mFlagMessage = "MonoIU: " ++ if mFlag then "on" else "off"
ex_ws1 :: [Work]
ex_ws1 = [WJug (Sub (TAll "a" (TArr (TVar "a") (TVar "a"))) (TAll "a" (TArr (TVar "a") (TVar "a"))))]

ws0 :: [Work]
ws0 = [WJug (Inf (Lam "x" (Lam "y" (ILit 1))) "a" End)]

ws1 :: [Work]
ws1 = [WJug (Inf (Ann (Lam "x" (App (App (Var "plus") (Var "x")) (ILit 1))) (TArr (TIntersection TInt TBool) TInt)) "a" End), WVar "plus" (TArr TInt (TArr TInt TInt))]

res1 :: (Bool, String)
res1 = bigStep False 0 40 "" ws1

res0 :: (Bool, String)
res0 = bigStep False 0 40 "" ws0

nondetEx1 :: [Work]
nondetEx1 = [WJug (Sub (TAll "a" (TUnion (TArr (TVar "a") TBool) (TArr (TVar "a") TInt))) (TUnion (TArr TInt TBool) (TArr TInt TInt)))]
