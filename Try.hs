import TestInfer
import InferLazyMF

abstractPoC :: Typ -> Typ
abstractPoC typ = abstractHelperPoC 0 typ []

abstractHelperPoC :: Int -> Typ -> [Typ] -> Typ
abstractHelperPoC n TInt typLs = TInt
abstractHelperPoC n TBool typLs = head typLs
abstractHelperPoC n (TForall t) typLs = TForall (\t -> abstractHelperPoC n t (t:typLs))
abstractHelperPoC 0 (TArrow t1 t2) typLs = TForall (\t -> TArrow t (abstractHelperPoC 1 t2 (t:typLs)))
abstractHelperPoC n (TArrow t1 t2) typLs = TArrow t1 (head typLs)
abstractHelperPoC n (TVar _) typLs = error ""

typ1 = TArrow TInt (TArrow TInt TBool)
absTyp1 = abstractPoC typ1

wl = [Sub typ1 absTyp1]
res = chkAndShow wl