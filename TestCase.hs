module TestCase where

import LazyDef


tEx = TVar . Right

ex1 = tEx 1
ex2 = tEx 2
ex3 = tEx 3

t1 = TForall (\a -> TArrow a a)

t2 = TArrow t1 (TForall (\a -> TArrow a a))

t3 = TArrow TInt TInt

t5 = TForall (\t -> t)

t6 = TArrow TInt TInt
t7 = TArrow t6 t6