let f :: (forall (a <: Int -> Int). a -> Int -> Int) = /\(a <: Int -> Int). \x -> \i -> x i in
	f (\x -> x) 1
