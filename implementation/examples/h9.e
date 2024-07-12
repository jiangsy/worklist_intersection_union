let f9 :: (forall a. Int -> a -> Int) -> Bool -> Int = \k -> k 3 in
let h9 :: (forall a. forall b. b -> a -> b) -> Bool -> Int = \k -> f9 k in h9

-- var f9: (k: <A>(x:number)=>(y:A)=>number) => (b: boolean) => number = k => k(3)
-- var h9: (k: <A,B>(x:B)=>(y:A)=>B) => (b: boolean) => number = k => f9(k)
