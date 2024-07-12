let f15 :: ((forall a. a -> a) -> Int) -> Int = \x -> 1 in
    let h15 :: (forall a. (a -> a) -> (a -> a)) -> Int = \x -> 1 in
        f15 h15 -- ex15

-- function f15(x: (_:<A>(_:A)=>A) => number) : number {return 1}
-- function h15(x:((_:<A>(_:A)=>A) => (<A>(_:A)=>A))) : number {return 1}
-- var ex15 = f15(h15)
