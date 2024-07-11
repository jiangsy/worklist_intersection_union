let ex12_2 :: (forall a. (a -> Bool) /\ (a -> Int)) -> Int = \x -> 1 in ex12_2

-- function ex12_2(x : <A>(((_:A)=>boolean) & ((_:A)=>number))) {...}  // rejected
