let f :: (forall (a <: Int -> Int). a -> Int -> Int) = /\(a <: Int -> Int). \x -> \i -> x i in
	f @(Int -> Int) (\x -> x) 1
