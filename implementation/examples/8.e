let fst1 :: forall a. forall b. a -> b -> a = /\a. /\b. \x -> \y -> x
    in (/\(a <: Int). \x -> fst1 @a x x) :: forall (a <: Int). a -> a
