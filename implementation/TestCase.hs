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

-- [forall 0. ((forall 1. ((1) -> 1)) -> 0) <: forall 0. ((forall 1. ((1) -> 1)) -> ((0) -> 0) -> 0)]
-- [forall 0. ((0) -> (0) -> 0) <: forall 0. ((0) -> forall 1. ((0) -> 0))]
-- [forall 0. ((forall 1. ((0) -> Int)) -> (Bool) -> Bool) <: ((Bool) -> Int) -> (Bool) -> Bool]

-- [forall 0. ((0) -> 0) <: forall 0. ((forall 1. ((0) -> 0)) -> 0)]
-- [(((Int) -> forall 0. ((Bool) -> 0)) -> Int) -> forall 0. ((0) -> 0) <: forall 0. ((forall 1. (((Int) -> (Bool) -> Bool) -> 1)) -> (0) -> 0)]
t10 = TForall $ \t0 -> TArrow t0 t0
t11 = TForall $ \t0 -> TArrow (TForall $ \t1 -> TArrow t0 t0) t0