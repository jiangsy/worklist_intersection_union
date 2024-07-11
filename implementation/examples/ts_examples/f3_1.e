let f3_1 :: ((Int -> Int -> Int) /\ (Int -> Bool -> Int)) -> Int = \f -> f 1 2 in f3_1

-- function f3_1(f: ((_:number) => (_:number) => number) & 
--                  ((_:number) => (_:boolean) => number)) { return f(1)(2) }
