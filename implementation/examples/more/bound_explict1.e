let f :: (forall (a <: Int). forall (b <: a). (b -> a) -> Int) = /\(a <: Int). /\(b <: a). \x -> 1 in
let g :: (forall a. a -> Int) = /\a. \x -> 1 in
	f @Int g
