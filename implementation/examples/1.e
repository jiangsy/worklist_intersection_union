let plus = \x -> \y -> 1
    in 
        let f :: (Int /\ Bool) -> Int = \x0 -> plus x0 1 in f
