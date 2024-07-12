let f6 = /\a. (\x -> 2) :: (a -> Int) -> Int in
    let g6 = (\f -> 1) :: (Int -> Int) -> Int in f6 g6 -- ex6

-- function f6(f: (_:<A>(_:A) => A) => number) { return 2 }
-- function g6(f: (_:number) => number) { return 1 }
-- var ex6 = f6(g6)
