let ex5_4 = (/\a. (\x -> \y -> \z -> 1) :: (a -> Int) -> (a -> Int) -> a -> Int) @(Int /\ Bool) ((\x -> 1) :: Int -> Int) ((\y -> 2) :: Bool -> Int) in ex5_4

-- function g5<A>(g1: (_:A) => number, g2: (_:A) => number): (x: A) => number { return x => 1 }
-- var ex5_4 = g5<number&boolean>((x: number) => 1, (y: boolean) => 2)