let snd1 :: forall a. forall b. a -> b -> b = /\a. /\b. \x -> \y -> y
    in snd1 1
