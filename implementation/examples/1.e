let map :: forall a. forall b. (a -> b) -> [a] -> [b] =
        /\ a. /\ b. \f -> \xs -> case xs of
                                    [] -> [];
                                    (y : ys) -> f y : map f ys
    in
        let plus = \x -> \y -> 1
            in map (\x -> plus x 1) (1 : 2 : 3 : [])
