module Syntax where

-- Algorithmic Types
data Typ
  = TInt
  | TBool
  | TTop
  | TBot
  | TVar String
  | TAll String Typ
  | TArr Typ Typ
  | TList Typ
  | TIntersection Typ Typ
  | TUnion Typ Typ
  | TLabel String
  deriving (Eq)

type TypPrec = Int

type ExpPrec = Int

baseTypPrec, arrTypPrec, intersectionTypPrec, unionTypPrec :: TypPrec
baseTypPrec = 0
arrTypPrec = 1
intersectionTypPrec = 2
unionTypPrec = 3

baseExpPrec, absExpPrec, appExpPrec :: ExpPrec
baseExpPrec = 0
absExpPrec = 1
appExpPrec = 2

addParen :: String -> String
addParen s = "(" ++ s ++ ")"

genTVarName :: Int -> String
genTVarName n = cycle ["a", "b", "c"] !! (n `mod` 3) ++ ("" : map show [0 ..]) !! (n `div` 3)

genVarName :: Int -> String
genVarName n = cycle ["x", "y"] !! (n `mod` 2) ++ ("" : map show [0 ..]) !! (n `div` 2)

genFreshTVar :: [String] -> String
genFreshTVar xs = head $ filter (`notElem` xs) $ map genTVarName [0 ..]

genFreshVar :: [String] -> String
genFreshVar xs = head $ filter (`notElem` xs) $ map genVarName [0 ..]

addParentP :: (TypPrec, TypPrec) -> Bool -> String -> String
addParentP (tp1, tp2) apFlag s
  | tp1 < tp2 = s
  | tp1 == tp2 && apFlag = s
  | otherwise = addParen s

showTyp :: Typ -> String
showTyp t = showTypHelper t baseTypPrec True
  where
    showTypHelper :: Typ -> TypPrec -> Bool -> String
    showTypHelper TInt _ _ = "Int"
    showTypHelper TBool _ _ = "Bool"
    showTypHelper TTop _ _ = "⊤"
    showTypHelper TBot _ _ = "⊥"
    showTypHelper (TVar x) _ _ = x
    showTypHelper (TAll x t) p _ =
      addParentP (p, baseTypPrec) True ("∀" ++ x ++ ". " ++ showTypHelper t baseTypPrec True)
    showTypHelper (TArr t1 t2) tp ap =
      addParentP (tp, arrTypPrec) ap (showTypHelper t1 arrTypPrec False ++ " → " ++ showTypHelper t2 arrTypPrec True)
    showTypHelper (TIntersection t1 t2) p ap =
      addParentP (p, intersectionTypPrec) ap (showTypHelper t1 intersectionTypPrec True ++ " ∩ " ++ showTypHelper t2 intersectionTypPrec False)
    showTypHelper (TUnion t1 t2) p ap =
      addParentP (p, unionTypPrec) ap (showTypHelper t1 unionTypPrec True ++ " ∪ " ++ showTypHelper t2 unionTypPrec False)
    showTypHelper (TList t) _ _ = "[" ++ showTypHelper t baseTypPrec True ++ "]"
    showTypHelper (TLabel x) _ _ = "(LABEL " ++ x ++ ")"

instance Show Typ where
  show = showTyp

-- Expressions
data Exp
  = Var String
  | ILit Integer
  | BLit Bool
  | Lam String Exp
  | App Exp Exp
  | Ann Exp Typ
  | TApp Exp Typ
  | TAbs String Exp
  | Nil
  | Cons Exp Exp
  | Case Exp Exp Exp
  | Fix Exp
  | Let String Exp Exp
  | LetA String Typ Exp Exp
  | RcdNil
  | RcdCons String Exp Exp
  | RcdProj Exp String
  deriving (Eq)

showExp :: Int -> Int -> Exp -> String
showExp ne nt e = showExpHelper e baseExpPrec True
  where
    showExpHelper :: Exp -> ExpPrec -> Bool -> String
    showExpHelper (Var x) _ _ = x
    showExpHelper (ILit n) _ _ = show n
    showExpHelper (BLit n) _ _ = show n
    showExpHelper (Lam x e) p ap = addParentP (p, absExpPrec) ap ("λ" ++ x ++ ". " ++ showExpHelper e absExpPrec True)
    showExpHelper (App e1 e2) p ap = addParentP (p, appExpPrec) ap (showExpHelper e1 appExpPrec False ++ " " ++ showExpHelper e2 appExpPrec True)
    showExpHelper (Ann e t) p ap = addParentP (p, baseExpPrec) ap (showExpHelper e baseExpPrec True ++ " :: " ++ show t)
    showExpHelper (TApp e t) p ap = addParentP (p, baseExpPrec) ap (showExpHelper e baseExpPrec True ++ " @" ++ show t)
    showExpHelper Nil _ _ = "[]"
    showExpHelper (Cons e1 e2) p ap = addParentP (p, baseExpPrec) ap (showExpHelper e1 baseExpPrec True ++ " : " ++ showExpHelper e2 baseExpPrec False)
    showExpHelper (Case e e1 e2) p ap = addParentP (p, baseExpPrec) ap ("case " ++ showExpHelper e baseExpPrec True ++ " of [] -> " ++ showExpHelper e1 baseExpPrec True ++ "; " ++ showExpHelper e2 baseExpPrec True)
    showExpHelper (Fix e) p ap = addParentP (p, baseExpPrec) ap ("fix " ++ showExpHelper e baseExpPrec True)
    showExpHelper (Let x e1 e2) p ap = addParentP (p, baseExpPrec) ap ("let " ++ x ++ " = " ++ showExpHelper e1 baseExpPrec True ++ " in " ++ showExpHelper e2 baseExpPrec True)
    showExpHelper (LetA x t e1 e2) p ap = addParentP (p, baseExpPrec) ap ("let " ++ x ++ " :: " ++ show t ++ " = " ++ showExpHelper e1 baseExpPrec True ++ " in " ++ showExpHelper e2 baseExpPrec True)
    showExpHelper RcdNil _ _ = "⟨⟩"
    showExpHelper (RcdCons l e1 e2) p ap = addParentP (p, baseExpPrec) ap (l ++ " ↦ " ++ showExpHelper e1 baseExpPrec True ++ ", " ++ showExpHelper e2 baseExpPrec False)
    showExpHelper (RcdProj e l) p ap = addParentP (p, baseExpPrec) ap (showExpHelper e baseExpPrec True ++ "." ++ l)

instance Show Exp where
  show = showExp 0 0

t1 = TArr TInt (TIntersection TInt TBool)

t2 = TIntersection (TArr TInt TInt) TBool

t3 = TIntersection (TAll "a" (TArr (TVar "a") (TVar "a"))) TInt

t4 = TAll "a" (TIntersection (TArr (TVar "a") (TVar "a")) TInt)

t5 = TArr (TArr TInt TInt) (TArr TInt TInt)

t6 = TArr (TArr TInt (TArr TInt TInt)) TInt

e1 = App (Lam "x" (Var "x")) (ILit 1)

e2 = Lam "x" (App (Var "x") (ILit 1))
