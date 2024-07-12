let f11 :: ((Int -> Int) /\ (Bool -> Bool)) -> Int = \g -> g 1 in
    f11 (\x -> x)

-- function f11(g: ((_:number)=>number) & ((_:boolean)=>boolean)): number { return 1 }
-- var ex11 = f11(x => x) // rejected!
