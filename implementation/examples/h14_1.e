-- accepted when MonoIU on; rejected when MonoIU off

let g14 :: (Int \/ Bool) -> (Int \/ Bool) -> Int = /\a. (\x -> \y -> 1) :: a -> a -> Int in
    let h14_1 :: Int -> Bool -> Int = g14 in h14_1

-- var f14: <A>(x: A) => (y: A) => number = x => y => 1
-- var g14: (x: number | boolean) => (y: number | boolean) => number = f14
-- var h14_1: (x: number) => (y: boolean) => number = g14
