{-# LANGUAGE FlexibleInstances #-}
module TestInfer where
import Test.QuickCheck
import System.Random (StdGen, mkStdGen, random)
import Control.Monad(liftM,liftM2,liftM3)

import InferLazyMF (Typ(..), Work(..), chk, t1, mono, chkAndShow)
import qualified InferSimple as InferS (Typ(..), Work(..), chk)

adaptTypStoLS :: InferS.Typ -> Typ
adaptTypStoLS (InferS.TVar e) = TVar e
adaptTypStoLS InferS.TInt = TInt
adaptTypStoLS InferS.TBool = TBool
adaptTypStoLS (InferS.TForall f) = TForall (adaptTypStoLS . f . adaptTypLStoS)
adaptTypStoLS (InferS.TArrow typ1 typ2) = TArrow (adaptTypStoLS typ1) (adaptTypStoLS typ2)

adaptTypLStoS :: Typ -> InferS.Typ
adaptTypLStoS (TVar e) = InferS.TVar e
adaptTypLStoS TInt = InferS.TInt
adaptTypLStoS TBool = InferS.TBool
adaptTypLStoS (TForall f) = InferS.TForall (adaptTypLStoS . f . adaptTypStoLS)
adaptTypLStoS (TArrow typ1 typ2) = InferS.TArrow (adaptTypLStoS typ1) (adaptTypLStoS typ2)

adaptWorkLStoS :: Work -> InferS.Work
adaptWorkLStoS (WVar n) = InferS.V (Left n)
adaptWorkLStoS (WExVar n typs typs') = InferS.V (Right n)
adaptWorkLStoS (Sub typ typ') = InferS.Sub (adaptTypLStoS typ) (adaptTypLStoS typ')

inferEqProp :: [Work] -> Bool
inferEqProp wl = chk wl == InferS.chk (map adaptWorkLStoS wl)

abstractHelper :: Typ -> [Typ] -> Typ
abstractHelper TInt typLs = TForall (\t -> t)
abstractHelper TBool typLs = TForall (\t -> t)
abstractHelper (TForall t) typLs = TForall (\t -> abstractHelper t (t:typLs))
abstractHelper (TArrow t1 t2) typLs = TArrow (abstractHelper t1 typLs) (abstractHelper t2 typLs)
abstractHelper (TVar _) typLs = error ""

abstract :: Typ -> Typ
abstract typ = abstractHelper typ []

-- https://www.seas.upenn.edu/~cis552/12fa/lectures/stub/QuickCheck.html
-- https://stackoverflow.com/questions/17615138/haskell-quickcheck-to-generate-and-test-rose-trees
-- https://www.cse.chalmers.se/~rjmh/QuickCheck/manual_body.html
monoTypGen :: Gen Typ
monoTypGen = sized monoNTypGen 
    where monoNTypGen 0 = elements [TBool, TInt]
          monoNTypGen n = oneof [liftM2 TArrow (monoNTypGen (n `div` 2)) (monoNTypGen (n `div` 2)),
                                 elements [TBool, TInt]
                                ]

instance Arbitrary Typ where
    arbitrary = monoTypGen

instance {-# OVERLAPPING #-} Arbitrary [Work] where
    arbitrary = do
                   leftTyp <- arbitrary
                   rightTyp <- arbitrary
                   frequency
                         [(2, return [Sub leftTyp (abstract leftTyp)]),
                          (1, return [Sub leftTyp rightTyp])]

test1 = chkAndShow [Sub (TArrow TInt (TArrow TInt TBool )) (TForall (\t -> (TArrow t (TArrow TInt t))))]