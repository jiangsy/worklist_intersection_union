let plus = \x -> \y -> 1
    in 
        let f1 :: Int \/ Bool -> Bool = \x -> plus x 1 in f1