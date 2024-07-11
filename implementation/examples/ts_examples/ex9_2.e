(\k -> k @ Bool 3) :: (forall a. forall b. b -> a -> b) -> Bool -> Int

-- var ex9_2: (k: <A,B>(x:B)=>(y:A)=>B) => (b:boolean) => number = k => k<boolean>(3) // rejected!
