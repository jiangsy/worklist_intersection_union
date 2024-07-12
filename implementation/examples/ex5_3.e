let g5 = /\a. (\x -> \y -> \z -> 1) :: (a -> Int) -> (a -> Int) -> a -> Int in
    g5 ((\x -> 1) :: Int -> Int) ((\y -> 2) :: Bool -> Int) -- ex5_3

-- function g5<A>(g1: (_:A) => number, g2: (_:A) => number): (x: A) => number { return x => 1 }
-- ex5_3 = g5((x: number) => 1, (y: boolean) => 2) // rejected!
