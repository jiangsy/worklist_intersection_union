let f8 :: ((forall a. a -> a -> Int) -> Int) -> Int = \x -> 1 in
let g8_3 :: ((Int /\ Bool) -> Int -> Int) -> Int = \f -> 1 in
    f8 g8_3 -- ex8_3

-- function f8(x: (_:<A>(_:A)=>(_:A)=>number)=>number): number { return 1 }
-- var g8_3 : (_:(_:(number&boolean))=>(_:number)=>number) => number = f => 1
-- var ex8_3 = f8(g8_3) // rejected!
