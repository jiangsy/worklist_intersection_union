let plus = \x -> \y -> 1
    in 
        let f1 :: (Int \/ Bool) -> Int = \x -> plus x 1 in f1
