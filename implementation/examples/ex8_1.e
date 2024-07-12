let f8 :: ((forall a. a -> a -> Int) -> Int) -> Int = \x -> 1 in
let g8_1 :: (Int -> (Int /\ Bool) -> Int) -> Int = \f -> 1 in
    f8 g8_1 -- ex8_1

-- function f8(x: (_:<A>(_:A)=>(_:A)=>number)=>number): number { return 1 }
-- var g8_1 : (_:(_:number)=>(_:number&boolean)=>number) => number = f => 1
-- var ex8_1 = f8(g8_1)
