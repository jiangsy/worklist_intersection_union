module TestCase where

import System.Random (StdGen, mkStdGen, next)
import LazyDef


tEx = TVar . Right

ex1 = tEx 1
ex2 = tEx 2
ex3 = tEx 3

t1 = TForall (\a -> TArrow a a)

t2 = TArrow t1 (TForall (\a -> TArrow a a))

t3 = TArrow TInt TInt

t5 = TForall (id)

t6 = TArrow TInt TInt
t7 = TArrow t6 t6

t8 = TForall $ \t -> TArrow TInt (TArrow t t)

t9 = TForall $ \t1 -> TArrow TInt (TForall (\t2 -> TArrow (TArrow t1 t2) t2))

t10 = TForall $ \t0 -> TArrow TInt (TArrow t0 t0)
t11 = TForall $ \t0 -> TArrow TInt (TForall $ \t1 -> TArrow (TArrow t0 t1) t1)


t12 = TForall $ \t0 -> TArrow (TArrow t0 (TArrow t0 t0)) t0
t13 = TForall $ \t0 -> TForall $ \t1 -> TArrow (TArrow t0 (TArrow t1 t0)) t0

t14 = TForall $ \t0 -> TArrow t0 (TForall $ \t1 -> TArrow t1 t0)
t15 = TForall $ \t0 -> TArrow t0 (TForall $ \t1 -> TArrow t0 t0)


t16 = TForall $ \t0 -> TArrow TInt TInt
t17 = TArrow TInt TInt

t18 = TForall $ \t0 -> TArrow t0 TBool
t19 = TForall $ \t0 -> TArrow (TArrow TBool t0) TBool 

t20 = TForall $ \t0 -> TArrow (TForall $ \t1 -> TArrow (TArrow t0 t1) t0) TInt
t21 = TArrow (TForall $ \t0 -> TArrow t0 TInt) TInt 

