let g1 :: (Label n -> Bool) -> Bool = \o -> o.n in
    let o1 = (m |-> 1, n |-> True, <>) in g1 o1 -- ex1_2

-- function g1(o: {n: boolean}): boolean { return o.n }
-- var o1 = {m: 1, n: true}; var ex1_2 = g1(o1)
