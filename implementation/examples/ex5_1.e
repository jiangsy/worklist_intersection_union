let f5 = /\a. (\x -> \y -> x) :: a -> a -> a in f5 1 True -- ex5_1

-- function f5<A>(x: A, y: A): A { return x }
-- var ex5_1 = f5(1, true) // rejected!
