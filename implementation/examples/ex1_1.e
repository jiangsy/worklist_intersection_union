let f1 :: (Label m -> Int) -> Int = \o -> o.m in
    let o1 = (m |-> 1, n |-> True, <>) in f1 o1

-- function f1(o: {m: number}): number { return o.m }
-- var o1 = {m: 1, n: true}; var ex1_1 = f1(o1);
