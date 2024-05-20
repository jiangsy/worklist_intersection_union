let fst1 :: forall a. forall b. a -> b -> a = /\a. /\b. \x -> \y -> x
    in (/\a. \x -> fst1 x x) :: forall a. a -> a
