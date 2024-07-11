let g9 :: (forall a. Int -> a -> Int) -> Bool -> Int = \k -> k @ Bool 3 in
    (\k -> g9 k) :: (forall a. forall b. b -> a -> b) -> Bool -> Int

-- var g9: (k: <A>(x:number)=>(y:A)=>number) => (b: boolean) => number = k => k<boolean>(3)
-- var ex9_1: (k: <A,B>(x:B)=>(y:A)=>B) => (b:boolean) => number = k => g9(k)
