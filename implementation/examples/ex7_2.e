let f7 = /\a. (\x -> x) :: a -> a in
    f7 @ (forall a. (a /\ a) -> (a \/ a)) f7 -- ex7_2

-- function f7<A>(x: A): A { return x }
-- var ex7_2 = f7<<A>(_:A&A)=>(A|A)>(f7)
