{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Alg where

import Data.List (delete, find, union)
import Data.Maybe (fromJust)
-- import Parser (parseExp)
import Syntax

-- Algorithmic Judgment
data Judgment
  = Sub Typ Typ
  | Chk Exp Typ
  | Inf Exp (Typ -> Judgment)
  | InfAbs Typ (Typ -> Typ -> Judgment)
  | InfApp Typ Typ Exp (Typ -> Judgment)
  | InfTApp Typ Typ (Typ -> Judgment)
  | CaseChk Exp Typ Typ
  | CaseInf Typ Exp Exp (Typ -> Judgment)
  | ConsInf Typ Exp (Typ -> Judgment)
  | End

instance Show Judgment where
  show c1 = show' c1 0
    where
      show' :: Judgment -> Int -> String
      show' (Sub a b) _ = show a ++ " <: " ++ show b
      show' (Chk e t) _ = show e ++ " <== " ++ show t
      show' (Inf e c) n =
        show e ++ " ==>" ++ show n ++ " " ++ show' (c (TVar $ show n)) (n + 1)
      show' (InfAbs a c) n =
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
  show (WTVar x TVarBind : w) = show w ++ ", " ++ x
  show (WTVar x STVarBind : w) = show w ++ ", ~" ++ x
  show (WTVar x ETVarBind : w) = show w ++ ", ^" ++ x
  show (WVar x t : w) = show w ++ ", " ++ x ++ " : " ++ show t
  show (WJug c : w) = show w ++ " ⊩ " ++ show c

eesubst :: String -> Exp -> Exp -> Exp
eesubst s e (Lam x b)
  | s == x = Lam x b
  | otherwise = Lam x (eesubst s e b)
eesubst s e (App e1 e2) = App (eesubst s e e1) (eesubst s e e2)
eesubst s e (Ann e1 t) = Ann (eesubst s e e1) t
eesubst s e (TApp e1 t) = TApp (eesubst s e e1) t
eesubst s e (TAbs x e1) = TAbs x (eesubst s e e1)
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
eesubst s e RcdNil = RcdNil
eesubst s e (RcdCons l1 e1 e2) = RcdCons l1 (eesubst s e e1) (eesubst s e e2)
eesubst s e (RcdProj e1 l1) = RcdProj (eesubst s e e1) l1

etsubst :: String -> Typ -> Exp -> Exp
etsubst e s (Lam x b) = Lam x (etsubst e s b)
etsubst e s (App e1 e2) = App (etsubst e s e1) (etsubst e s e2)
etsubst e s (Ann e1 t) = Ann (etsubst e s e1) (ttsubst e s t)
etsubst e s (TApp e1 t) = TApp (etsubst e s e1) (ttsubst e s t)
etsubst e s (TAbs x e1) = TAbs x (etsubst e s e1)
etsubst e s (Cons e1 e2) = Cons (etsubst e s e1) (etsubst e s e2)
etsubst e s (Case e1 e2 e3) = Case (etsubst e s e1) (etsubst e s e2) (etsubst e s e3)
etsubst e s (Fix e1) = Fix (etsubst e s e1)
etsubst e s (Let x e1 e2) = Let x (etsubst e s e1) (etsubst e s e2)
etsubst e s (LetA x t e1 e2) = LetA x (ttsubst e s t) (etsubst e s e1) (etsubst e s e2)
etsubst e s RcdNil = RcdNil
etsubst e s (RcdCons l1 e1 e2) = RcdCons l1 (etsubst e s e1) (etsubst e s e2)
etsubst e s (RcdProj e1 l1) = RcdProj (etsubst e s e1) l1

ttsubst :: String -> Typ -> Typ -> Typ
ttsubst _ _ TInt = TInt
ttsubst _ _ TBool = TBool
ttsubst _ _ TTop = TTop
ttsubst _ _ TBot = TBot
ttsubst s t (TVar x)
  | s == x = t
  | otherwise = TVar x
ttsubst s t (TAll a c)
  | s == a = TAll a c
  | otherwise = TAll a (ttsubst s t c)
ttsubst s t (TArr t1 t2) =
  TArr (ttsubst s t t1) (ttsubst s t t2)
ttsubst s t (TList t1) = TList (ttsubst s t t1)

ctsubst :: String -> Typ -> Judgment -> Judgment
ctsubst s t (Sub a b) = Sub (ttsubst s t a) (ttsubst s t b)
ctsubst s t (Chk e a) = Chk (etsubst s t e) (ttsubst s t a)
ctsubst s t (Inf e f) = Inf (etsubst s t e) (ctsubst s t . f)
ctsubst s t (InfAbs t1 f) = InfAbs (ttsubst s t t1) (\a b -> ctsubst s t (f a b))
ctsubst s t (InfApp t1 t2 e f) = InfApp (ttsubst s t t1) (ttsubst s t t2) (etsubst s t e) (ctsubst s t . f)
ctsubst s t (InfTApp t1 t2 f) = InfTApp (ttsubst s t t1) (ttsubst s t t2) (ctsubst s t . f)
ctsubst s t (CaseChk e a b) = CaseChk (etsubst s t e) (ttsubst s t a) (ttsubst s t b)
ctsubst s t (CaseInf t1 e e1 f) = CaseInf (ttsubst s t t1) (etsubst s t e) (etsubst s t e1) (ctsubst s t . f)
ctsubst s t (ConsInf t1 e f) = ConsInf (ttsubst s t t1) (etsubst s t e) (ctsubst s t . f)
ctsubst _ _ End = End

ftvarInTyp :: Typ -> [String]
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

tvarInTyp :: Typ -> [String]
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

genSplit :: [Char] -> ([Char], [Char])
genSplit x = (x ++ "1", x ++ "2")

findVar :: String -> Worklist -> Maybe Typ
findVar x (WVar y a : w)
  | x == y = Just a
  | otherwise = findVar x w
findVar x (_ : w) = findVar x w
findVar _ [] = Nothing

tvarInTyps = foldl union [] . map tvarInTyp

pickNewTVar :: [Work] -> [Typ] -> [Char]
pickNewTVar ws ts = genFreshTVar (wvars `union` tvarInTyps ts)
  where
    wvars =
      concatMap
        ( \case
            WTVar v _ -> [v]
            _ -> []
        )
        ws

expVar :: Exp -> [String]
expVar (Var x) = [x]
expVar (Lam x b) = x : expVar b
expVar (App e1 e2) = expVar e1 ++ expVar e2
expVar (Cons e1 e2) = expVar e1 ++ expVar e2
expVar (Case e1 e2 e3) = expVar e1 ++ expVar e2 ++ expVar e3
expVar (Fix e) = expVar e
expVar _ = []

pickNewVar :: Foldable t => Exp -> t Work -> String
pickNewVar e w = fromJust $ find (`notElem` wvars) bvarsupply
  where
    wvars =
      concatMap
        ( \case
            WVar v _ -> [v]
            _ -> []
        )
        w
        ++ expVar e
    bvarsupply = "x" : "y" : [xy : show @Integer n | n <- [1 .. 100], xy <- ['x', 'y']]

findTVar :: [Work] -> String -> TBind
findTVar w a = head [t | WTVar a' t <- w, a == a']

mono :: [Work] -> Typ -> Bool
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

curInfo :: [Work] -> String -> String
curInfo ws s1 = "   " ++ show (reverse ws) ++ "\n-->{ Rule: " ++ s1 ++ replicate (20 - length s1) ' ' ++ " }\n"

bigStep :: String -> [Work] -> (Bool, String)
bigStep info [] = (True, info)
bigStep info (WTVar x _ : ws) = bigStep (info ++ curInfo ws "GCTVar") ws
bigStep info (WVar x _ : ws) = bigStep (info ++ curInfo ws "GCVar") ws
--
--
-- Subtyping
--
--
bigStep info (WJug (Sub _ TTop) : ws) = bigStep (info ++ curInfo ws "≤⊤") ws
bigStep info (WJug (Sub TBot _) : ws) = bigStep (info ++ curInfo ws "≤⊥") ws
bigStep info (WJug (Sub TInt TInt) : ws) = bigStep (info ++ curInfo ws "≤Int") ws
bigStep info (WJug (Sub TBool TBool) : ws) = bigStep (info ++ curInfo ws "≤Bool") ws
bigStep info (WJug (Sub (TVar x) (TVar y)) : ws)
  | x == y = bigStep (info ++ curInfo ws "≤TVar") ws
bigStep info (WJug (Sub (TArr t1 t2) (TArr t3 t4)) : ws) = bigStep (info ++ curInfo ws' "≤→") ws'
  where
    ws' = WJug (Sub t2 t4) : WJug (Sub t3 t1) : ws
bigStep info (WJug (Sub (TAll a t1) (TAll b t2)) : ws) = bigStep (info ++ curInfo ws' "≤∀") ws'
  where
    c = pickNewTVar ws [t1, t2]
    t1' = ttsubst a (TVar c) t1
    t2' = ttsubst b (TVar c) t2
    ws' = WJug (Sub t1' t2') : WTVar b STVarBind : ws
bigStep info (WJug (Sub (TAll a t1) t2) : ws)
  | notUnion t2 && notIntersection t2 = bigStep (info ++ curInfo ws' "≤∀L") ws'
  where
    b = pickNewTVar ws [t1]
    t1' = ttsubst a (TVar b) t1
    ws' = WJug (Sub t1' t2) : WTVar b ETVarBind : ws
bigStep info (WJug (Sub (TVar a) t) : w)
  | mono w t && findTVar w a == ETVarBind && (a `notElem` ftvarInTyp t) = bigStep (info ++ curInfo ws' "≤MonoL") ws'
  where
    ws' = substWL a t w
bigStep info (WJug (Sub t (TVar a)) : w)
  | mono w t && findTVar w a == ETVarBind && (a `notElem` ftvarInTyp t) = bigStep (info ++ curInfo ws' "≤MonoR") ws'
  where
    ws' = substWL a t w
bigStep info (WJug (Sub (TVar a) (TArr t1 t2)) : ws)
  | not (mono ws (TArr t1 t2)) && findTVar ws a == ETVarBind = bigStep (info ++ curInfo ws' "≤SplitL") ws'
  where
    a1 = pickNewTVar ws []
    a2 = pickNewTVar ws [TVar a1]
    ws' = WJug (Sub (TArr (TVar a1) (TVar a2)) (TArr t1 t2)) : substWL a (TArr (TVar a1) (TVar a2)) (WTVar a2 ETVarBind : WTVar a1 ETVarBind : ws)
bigStep info (WJug (Sub (TArr t1 t2) (TVar a)) : ws)
  | not (mono ws (TArr t1 t2)) && findTVar ws a == ETVarBind = bigStep (info ++ curInfo ws' "≤SplitL") ws'
  where
    a1 = pickNewTVar ws []
    a2 = pickNewTVar ws [TVar a1]
    ws' = WJug (Sub (TArr (TVar a1) (TVar a2)) (TArr t1 t2)) : substWL a (TArr (TVar a1) (TVar a2)) (WTVar a2 ETVarBind : WTVar a1 ETVarBind : ws)
bigStep info (WJug (Sub t1 (TIntersection t2 t3)) : w) = bigStep (info ++ curInfo ws' "≤∩R") ws'
  where
    ws' = WJug (Sub t1 t3) : WJug (Sub t1 t2) : w
bigStep info (WJug (Sub (TIntersection t11 t12) t2) : ws) = case bigStep info (WJug (Sub t11 t2) : ws) of
  (True, info) -> (True, info ++ curInfo (WJug (Sub t11 t2) : ws) "≤∩L1")
  (False, info) -> bigStep (info ++ curInfo (WJug (Sub t12 t2) : ws) "≤∩L2") (WJug (Sub t12 t2) : ws)
bigStep info (WJug (Sub (TUnion t11 t12) t2) : ws) = bigStep (info ++ curInfo ws' "≤∪L") ws'
  where
    ws' = WJug (Sub t11 t2) : WJug (Sub t12 t2) : ws
bigStep info (WJug (Sub t1 (TUnion t21 t22)) : ws) = case bigStep (info ++ curInfo (WJug (Sub t1 t21) : ws) "≤∪R1") (WJug (Sub t1 t21) : ws) of
  (True, info) -> (True, info)
  (False, s) -> bigStep (info ++ curInfo (WJug (Sub t1 t22) : ws) "≤∪R2") (WJug (Sub t1 t22) : ws)
--
-- New Subtyping
--
bigStep info _ = (False, info)

-- step (WJug (Sub (TIntersection t1 t2) t3) : w) = WJug (Sub t1 t3) : w
-- step (WJug (Sub (TIntersection t1 t2) t3) : w) = WJug (Sub t1 t3) : w
-- bigStep n info (Sub (TForall g) b : ws)             = bigStep (n+1) (info ++ curInfo ws' "SForallL") ws'
--                                                         where ws' = Sub (g (TVar (Right n))) b: WExVar n TBot TTop : ws

-- bigStep n info (Sub (TVar (Right i)) (TArrow a b) : ws)
--   | not $ mono (TArrow a b)                         = case carryBackInWL (TVar (Right i)) a1_a2 (Sub a1_a2 (TArrow a b) :
--                                                                                                  WExVar (n+1) TBot TTop :
--                                                                                                  WExVar n TBot TTop : ws)
--                                                            >>= updateBoundInWL (TVar (Right i)) (UB, a1_a2) of
--                                                         Left error -> (False, info++error)
--                                                         Right ws' -> bigStep (n+2) (info ++ curInfo ws' "SplitL") ws'
--                                                       where
--                                                         a1 = TVar (Right n)
--                                                         a2 = TVar $ Right (n + 1)
--                                                         a1_a2 = TArrow a1 a2
-- bigStep n info (Sub (TArrow a b) (TVar (Right i)) : ws)
--   | not $ mono (TArrow a b)                         = case carryBackInWL (TVar (Right i)) a1_a2 (Sub (TArrow a b) a1_a2 :
--                                                                                                  WExVar (n+1) TBot TTop :
--                                                                                                  WExVar n TBot TTop : ws)
--                                                           >>= updateBoundInWL (TVar (Right i)) (LB, a1_a2) of
--                                                         Left error -> (False, info ++ error)
--                                                         Right ws' -> bigStep (n+1) (info ++ curInfo ws' "SplitR") ws'
--                                                       where
--                                                         a1 = TVar (Right n)
--                                                         a2 = TVar $ Right (n + 1)
--                                                         a1_a2 = TArrow a1 a2

-- bigStep n info (Sub vi@(TVar (Right i)) vj@(TVar (Right j)) : ws)                                       -- 15 & 16
--   | prec ws vi vj                                   = case carryBackInWL vj vi ws >>= updateBoundInWL vj (UB, vi) of
--                                                         Left error -> (False, info++error)
--                                                         Right ws' -> bigStep n (info++curInfo ws' "SolveLExtVar") ws'
--   | prec ws vj vi                                   = case carryBackInWL vi vj ws >>= updateBoundInWL vi (UB, vj) of
--                                                         Left error -> (False, info ++ error)
--                                                         Right ws' -> bigStep n (info++curInfo ws' "SolveRExtVar") ws'

-- bigStep n info (Sub (TVar (Right i)) t : ws)                                        -- 11
--   | mono t                                          = case carryBackInWL (TVar (Right i)) t ws >>=
--                                                           updateBoundInWL (TVar (Right i)) (UB, t) of
--                                                         Left error -> (False, info ++ error)
--                                                         Right ws' -> bigStep n (info++curInfo ws' "SolveMonoL") ws'

-- bigStep n info (Sub t (TVar (Right i))  : ws)                                       -- 12
--   | mono t                                          = case carryBackInWL (TVar (Right i)) t ws >>=
--                                                           updateBoundInWL (TVar (Right i)) (LB, t) of
--                                                         Left error -> (False, info++error)
--                                                         Right ws' -> bigStep n (info++curInfo ws' "SolveMonoR") ws'

-- bigStep n info (Sub t1 (TIntersection t21 t22) : ws) = bigStep n (info ++ curInfo ws' "SIntersection") ws'
--                                                           where ws' = Sub t1 t21 : Sub t1 t22 : ws
-- bigStep n info (Sub (TIntersection t11 t12) t2 : ws) = case bigStep n info (Sub t11 t2 : ws) of
--                                                           (True, info) -> (True, info++curInfo (Sub t11 t2 : ws) "SIntersection")
--                                                           (False, info) -> bigStep n (info ++ curInfo (Sub t12 t2 : ws) "SIntersection") (Sub t12 t2 : ws)

-- bigStep n info (Sub (TUnion t11 t12) t2 : ws)        = bigStep n (info ++ curInfo ws' "SUnion") ws'
--                                                           where ws' = Sub t11 t2 : Sub t12 t2 : ws
-- bigStep n info (Sub t1 (TUnion t21 t22) : ws)        = case bigStep n info (Sub t1 t21 : ws) of
--                                                           (True, info) -> (True, info++curInfo (Sub t1 t21 : ws) "SUnion")
--                                                           (False, s) -> bigStep n (info++curInfo (Sub t1 t22 : ws) "SUnion") (Sub t1 t22 : ws)

-- bigStep _ info _                                     = (False, info)

-- step :: Worklist -> Worklist
-- -- Garbage collection
-- step (WTVar _ _ : w) = w
-- step (WVar _ _ : w) = w
-- -- Subtyping
-- step (WJug (Sub TInt TInt) : w) = w
-- step (WJug (Sub TBool TBool) : w) = w
-- step (WJug (Sub (TVar a) (TVar b)) : w)
--   | a == b = w
-- step (WJug (Sub _ TTop) : w) = w
-- step (WJug (Sub TBot _) : w) = w
-- step (WJug (Sub (TArr t1 t2) (TArr t3 t4)) : w) = WJug (Sub t3 t1) : WJug (Sub t2 t4) : w
-- step (WJug (Sub (TAll a t1) (TAll b t2)) : w) = WJug (Sub t1' t2') : WTVar c STVarBind : w
--   where
--     c = pickNewTVar w
--     t1' = ttsubst a (TVar c) t1
--     t2' = ttsubst b (TVar c) t2
-- step (WJug (Sub (TAll a t1) t2) : w)
--   | notIntersection t2 && notUnion t2 = WJug (Sub t1' t2) : WTVar b ETVarBind : w
--   where
--     b = pickNewTVar w
--     t1' = ttsubst a (TVar b) t1
-- step (WJug (Sub (TVar a) t) : w)
--   | mono w t && findTVar w a == ETVarBind && (a `notElem` ftvarInTyp t) = substWL a t w
-- step (WJug (Sub t (TVar a)) : w)
--   | mono w t && findTVar w a == ETVarBind && (a `notElem` ftvarInTyp t) = substWL a t w
-- step (WJug (Sub (TVar a) (TArr b c)) : w)
--   | not (mono w (TArr b c)) && findTVar w a == ETVarBind =
--       WJug (Sub (TArr (TVar a1) (TVar a2)) (TArr b c)) : substWL a (TArr (TVar a1) (TVar a2)) (WTVar a2 ETVarBind : WTVar a1 ETVarBind : w)
--   where
--     (a1, a2) = genSplit a
-- step (WJug (Sub (TArr b c) (TVar a)) : w)
--   | not (mono w (TArr b c)) && findTVar w a == ETVarBind =
--       WJug (Sub (TArr b c) (TArr (TVar a1) (TVar a2))) : substWL a (TArr (TVar a1) (TVar a2)) (WTVar a2 ETVarBind : WTVar a1 ETVarBind : w)
--   where
--     (a1, a2) = genSplit a
-- step (WJug (Sub t1 (TIntersection t2 t3)) : w) = WJug (Sub t1 t3) : WJug (Sub t1 t2) : w
-- step (WJug (Sub (TIntersection t1 t2) t3) : w) = WJug (Sub t1 t3) : w
-- step (WJug (Sub (TIntersection t1 t2) t3) : w) = WJug (Sub t1 t3) : w

-- -- List subtyping
-- step (WJug (Sub (TList a) (TList b)) : w) = WJug (Sub a b) : w
-- step (WJug (Sub (TVar a) (TList b)) : w)
--   | findTVar w a == ETVarBind = WJug (Sub (TVar x) b) : substWL a (TList (TVar x)) (WTVar x ETVarBind : w)
--   where
--     x = pickNewTVar w
-- step (WJug (Sub (TList b) (TVar a)) : w)
--   | findTVar w a == ETVarBind = WJug (Sub (TVar x) b) : substWL a (TList (TVar x)) (WTVar x ETVarBind : w)
--   where
--     x = pickNewTVar w

-- -- Checking
-- step (WJug (Chk (Lam x e) (TArr t1 t2)) : w) = WJug (Chk e' t2) : WVar y t1 : w
--   where
--     y = pickNewVar e w
--     e' = eesubst x (Var y) e
-- step (WJug (Chk (Lam x e) TTop) : w) = WJug (Chk e' TTop) : WVar y TBot : w
--   where
--     y = pickNewVar e w
--     e' = eesubst x (Var y) e
-- step (WJug (Chk (Lam x e) (TVar a)) : w)
--   | findTVar w a == ETVarBind =
--       WJug (Chk e' (TVar a2)) : WVar y (TVar a1) : substWL a (TArr (TVar a1) (TVar a2)) (WTVar a2 ETVarBind : WTVar a1 ETVarBind : w)
--   where
--     (a1, a2) = genSplit a
--     y = pickNewVar e w
--     e' = eesubst x (Var y) e
-- -- List checking
-- step (WJug (Chk Nil (TList _)) : w) = w
-- step (WJug (Chk (Cons e1 e2) (TList a)) : w) = WJug (Chk e1 a) : WJug (Chk e2 (TList a)) : w
-- step (WJug (CaseChk e (TList a) b) : w) = WJug (Chk e (TArr a (TArr (TList a) b))) : w
-- step (WJug (Chk (Case e e1 e2) b) : w) = WJug (Chk e1 b) : WJug (Inf e (\a -> CaseChk e2 a b)) : w
-- -- Fix checking
-- step (WJug (Chk (Fix e) a) : w) = WJug (Chk e (TArr a a)) : w
-- -- Let checking
-- step (WJug (Chk (LetA x t e1 e2) b) : w) = WJug (Chk (App (Ann (Lam x e2) (TArr t b)) (Ann (Fix (Lam x e1)) t)) b) : w
-- -- Subsumption checking
-- step (WJug (Chk e b) : w) = WJug (Inf e (`Sub` b)) : w
-- -- Inference --
-- step (WJug (Inf (Var x) c) : w) = case findVar x w of
--   Just a -> WJug (c a) : w
--   Nothing -> error $ "No binding for " ++ x
-- step (WJug (Inf (Ann e a) c) : w) = WJug (Chk e a) : WJug (c a) : w
-- step (WJug (Inf (ILit _) c) : w) = WJug (c TInt) : w
-- step (WJug (Inf (BLit _) c) : w) = WJug (c TBool) : w
-- step (WJug (Inf (App e1 e2) c) : w) = WJug (Inf e1 (\b -> InfAbs b (\d1 d2 -> InfApp d1 d2 e2 c))) : w
-- step (WJug (Inf (TApp e t) c) : w) = WJug (Inf e (\b -> InfTApp b t c)) : w
-- step (WJug (Inf (Lam x e) c) : w) =
--   WJug (Chk e' (TVar b)) : WVar y (TVar a) : WJug (c (TArr (TVar a) (TVar b))) : WTVar b ETVarBind : WTVar a ETVarBind : w
--   where
--     a = pickNewTVar w
--     b = pickNewTVar (WTVar a ETVarBind : w)
--     y = pickNewVar e w
--     e' = eesubst x (Var y) e
-- -- Type abstraction inference
-- step (WJug (Inf (TAbs a (Ann e t)) c) : w) =
--   WJug (Chk e' t') : WTVar a' TVarBind : WJug (c (TAll a' t')) : w
--   where
--     a' = pickNewTVar w
--     e' = etsubst a (TVar a') e
--     t' = ttsubst a (TVar a') t
-- -- \*** new rules
-- step (WJug (Inf (TAbs a e) c) : w) =
--   WJug (Inf e' (c . TAll a')) : WTVar a' TVarBind : w
--   where
--     a' = pickNewTVar w
--     e' = etsubst a (TVar a') e
-- -- Matching
-- step (WJug (InfAbs (TArr a b) c) : w) = WJug (c a b) : w
-- step (WJug (InfAbs TBot c) : w) = WJug (c TTop TBot) : w
-- step (WJug (InfAbs (TAll a t) c) : w) = WJug (InfAbs t' c) : WTVar x ETVarBind : w
--   where
--     x = pickNewTVar w
--     t' = ttsubst a (TVar x) t
-- step (WJug (InfAbs (TVar a) c) : w)
--   | findTVar w a == ETVarBind =
--       substWL a (TArr (TVar a1) (TVar a2)) (WJug (InfAbs (TArr (TVar a1) (TVar a2)) c) : WTVar a2 ETVarBind : WTVar a1 ETVarBind : w)
--   where
--     (a1, a2) = genSplit a
-- -- Dummy Application Inference
-- step (WJug (InfApp t1 t2 e c) : w) = WJug (Chk e t1) : WJug (c t2) : w
-- -- Type application inference
-- step (WJug (InfTApp (TAll a t1) t2 c) : w) = WJug (c (ttsubst a t2 t1)) : w
-- step (WJug (InfTApp TBot _ c) : w) = WJug (c TBot) : w
-- -- list rules
-- step (WJug (Inf Nil c) : w) = WJug (c (TAll x (TList (TVar x)))) : w
--   where
--     x = pickNewTVar w
-- step (WJug (Inf (Cons e1 e2) c) : w) = WJug (Inf e1 (\b -> ConsInf b e2 c)) : w
-- step (WJug (Inf (Case e e1 e2) c) : w) = WJug (Inf e1 (\b -> CaseInf b e e2 c)) : w
-- step (WJug (ConsInf b e c) : w) = WJug (Chk e (TList b)) : WJug (c b) : w
-- step (WJug (CaseInf b e e2 c) : w) = WJug (Inf e (\a -> CaseChk e2 a b)) : WJug (c b) : w
-- -- fix
-- step (WJug (Inf (Fix e) c) : w) = WJug (Chk e (TArr (TVar a) (TVar a))) : WJug (c (TVar a)) : WTVar a ETVarBind : w
--   where
--     a = pickNewTVar w
-- -- let
-- step (WJug (Inf (Let x e1 e2) c) : w) = WJug (Inf (App (Lam x e2) (Fix (Lam x e1))) c) : w
-- step (WJug (Inf (LetA x t e1 e2) c) : w) = WJug (Inf e2 c) : WJug (Chk e1 t) : WVar x t : w
-- -- ret
-- step (WJug End : w) = w
-- step w = error $ "No rule matching " ++ show w

-- runStep :: Worklist -> IO ()
-- runStep [] = putStrLn "Done."
-- runStep w = do
--   print w
--   runStep (step w)

-- run :: FilePath -> IO ()
-- run s = do
--   code <- readFile s
--   case parseExp code of
--     Left err -> putStrLn err
--     Right e -> runStep [WJug (Inf e (const End))]
