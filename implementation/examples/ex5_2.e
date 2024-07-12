let f5 = /\a. (\x -> \y -> x) :: a -> a -> a in f5 @ (Bool \/ Int) 1 True -- ex5_2

-- function f5<A>(x: A, y: A): A { return x }
-- var ex5_2 = f5<boolean|number>(1, true)
