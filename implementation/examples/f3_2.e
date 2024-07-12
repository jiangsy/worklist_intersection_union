let f3_2 :: ((Int -> Int -> Int) /\ (Int -> Bool -> Int)) -> Int = \f -> f 1 True in f3_2

-- function f3_2(f: ((_:number) => (_:number) => number) & 
--                  ((_:number) => (_:boolean) => number)) { return f(1)(true) } // rejected
