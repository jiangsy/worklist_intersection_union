let h1 :: (((Label m -> Int) /\ (Label n -> Bool)) \/ ((Label k -> Int -> Int) /\ (Label m -> Int))) -> Int = \o -> o.m in h1

-- function h1(o: {m: number, n: boolean} | {k: string, m: number}): number { return o.m }
