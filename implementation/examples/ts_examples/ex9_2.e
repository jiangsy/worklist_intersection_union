let ex9_2 :: (forall a. forall b. b -> a -> b) -> Bool -> Int = \k -> k @ Bool 3 in ex9_2

-- var ex9_2: (k: <A,B>(x:B)=>(y:A)=>B) => (b:boolean) => number = k => k<boolean>(3) // rejected!
