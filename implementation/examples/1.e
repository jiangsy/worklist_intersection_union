let plus = \x -> \y -> 1
    in 
        let f :: Int -> Int = \x0 -> plus x0 1 in f
