let f7 = /\a. (\x -> x) :: a -> a in
    f7 @ (forall a. a -> a) f7 -- ex7_1

-- function f7<A>(x: A): A { return x }
-- var ex7_1 = f7<<A>(_:A)=>A>(f7)
