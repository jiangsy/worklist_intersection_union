let f2 :: ((Int -> Int) /\ (Bool -> Bool)) -> Bool = \g -> g True in f2

-- function f2(g: ((_:number) => number) & ((_:boolean) => boolean)) { return g(true) }
