let idFun :: forall (a <: Int). forall (b <: a -> a). b -> a -> a = /\(a <: Int). /\(b <: a -> a). \x -> x
    in
        let idInt :: Int -> Int = \x -> x
            in idFun idInt
