let map :: forall a. forall b. (a -> b) -> [a] -> [b] =
    /\a. (/\b. (\f -> \xs -> case xs of
                                [] -> [];
                                (y : ys) -> f y : map f ys) :: (a -> b) -> [a] -> [b])
    in map @(Int \/ Bool) ((\x -> 1) :: (Int \/ Bool) -> Int) ((False : 1 : []) :: [Int \/ Bool])
