let f8 :: ((forall a. a -> a -> Int) -> Int) -> Int = \x -> 1 in
let g8_4 :: (Int -> (Int \/ Bool) -> Int) -> Int = \f -> 1 in
    f8 g8_4 -- ex8_4

-- function f8(x: (_:<A>(_:A)=>(_:A)=>number)=>number): number { return 1 }
-- var g8_4: (_:(_:number)=>(_:number|boolean)=>number) => number = f => 1
-- var ex8_4 = f8(g8_4) // rejected!
