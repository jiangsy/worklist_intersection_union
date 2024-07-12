let f10 :: (Int -> Int) -> Int = \x -> 1 in
let h10 = (\x -> \y -> y) 1 in
    f10 h10 -- ex10

-- function f10(g: ((_:number) => number)): number { return 1 }
-- var g10 = x => y => y; var h10 = g10(1)
-- var ex10 = f10(h10) // accepted, but with wrong type inferred for h10
