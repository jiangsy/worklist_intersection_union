let k :: (Int -> Int) -> Int = \f -> 1
    in
        let g :: ((forall (a <: Int). a -> a) -> Int) -> Int = \f -> 1
            in g k
