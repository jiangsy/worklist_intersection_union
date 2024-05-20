let plus :: Int -> Int -> Int = \x -> \y -> 1
    in
        let fPlus :: forall a. (a -> Int) -> (a -> Int) -> Int =
            /\a. \f -> \g -> \x -> plus (f x) (g x)
        in
            fPlus ((\x -> plus x 1) :: Int -> Int) ((\y -> 5) :: Bool -> Int)
