let f :: ((Label m -> Int) /\ (Label n -> Bool)) -> Int = \x -> x.m in f
