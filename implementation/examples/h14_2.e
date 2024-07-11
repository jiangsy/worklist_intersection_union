let h14_2 :: Int -> Bool -> Int = /\a. (\x -> \y -> 1) :: a -> a -> Int in h14_2

-- var f14: <A>(x: A) => (y: A) => number = x => y => 1
-- var g14: (x: number | boolean) => (y: number | boolean) => number = f14
-- var h14_2: (x: number) => (y: boolean) => number = f14 // rejected!
