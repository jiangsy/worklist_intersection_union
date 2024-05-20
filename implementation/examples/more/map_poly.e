let map :: forall a. forall b. (a -> b) -> [a] -> [b] =
    /\a. /\b. \f -> \xs -> case xs of
                                [] -> [];
                                (y : ys) -> f y : map f ys
    in let plist :: [forall a. a -> a] = (/\a. \z -> z) : (/\a. \z -> z) : []
       in map @(forall a. a -> a) (\f -> f 1) plist
