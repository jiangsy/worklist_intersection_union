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

baseTypPrec, arrTypPrec, intersectionTypPrec, unionTypPrec :: TypPrec
baseTypPrec = 0
arrTypPrec = 1
intersectionTypPrec = 2
unionTypPrec = 3

addParen :: String -> String
addParen s = "(" ++ s ++ ")"

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

instance Show Exp where
  show (Var x) = x
  show (ILit n) = show n
  show (BLit n) = show n
  show (Lam x e) = "λ" ++ x ++ ". " ++ show e
  show (App e1 e2) = showExp e1 ++ " " ++ showExp e2
  show (Ann e t) = showExp e ++ " :: " ++ show t
  show (TApp e t) = showExp e ++ " @" ++ show t
  show (TAbs x e) = "Λ" ++ x ++ ". " ++ show e
  show Nil = "[]"
  show (Cons e1 e2) = show e1 ++ " : " ++ show e2
  show (Case e e1 e2) = "case " ++ show e ++ " of [] -> " ++ show e1 ++ "; " ++ show e2
  show (Fix e) = "fix " ++ show e
  show (Let x e1 e2) = "let " ++ x ++ " = " ++ show e1 ++ " in " ++ show e2
  show (LetA x t e1 e2) = "let " ++ x ++ " :: " ++ show t ++ " = " ++ show e1 ++ " in " ++ show e2
  show RcdNil = "⟨⟩"
  show (RcdCons l e1 e2) = l ++ " ↦ " ++ show e1 ++ ", " ++ show e2
  show (RcdProj e l) = show e ++ "." ++ show l

showExp :: Exp -> String
showExp e = case e of
  Lam {} -> showParens $ show e
  Ann {} -> showParens $ show e
  TAbs {} -> showParens $ show e
  Cons {} -> showParens $ show e
  Case {} -> showParens $ show e
  Fix {} -> showParens $ show e
  Let {} -> showParens $ show e
  LetA {} -> showParens $ show e
  RcdCons {} -> showParens $ show e
  _ -> show e

showParens :: String -> String
showParens s = "(" ++ s ++ ")"

t1 = TArr TInt (TIntersection TInt TBool)

t2 = TIntersection (TArr TInt TInt) TBool

t3 = TIntersection (TAll "X" (TArr (TVar "X") (TVar "X"))) TInt

t4 = TAll "X" (TIntersection (TArr (TVar "X") (TVar "X")) TInt)

t5 = TArr (TArr TInt TInt) (TArr TInt TInt)

t6 = TArr (TArr TInt (TArr TInt TInt)) TInt