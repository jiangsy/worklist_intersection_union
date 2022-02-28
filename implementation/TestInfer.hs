{-# LANGUAGE FlexibleInstances, MultiWayIf, ScopedTypeVariables #-}
module TestInfer where
import Data.Time.Clock
import Test.QuickCheck
import System.Random(StdGen, mkStdGen, random, randomR, randomRs, RandomGen)
import System.IO.Unsafe
import Control.Monad(liftM,liftM2,liftM3)
import Data.Functor

import LazyDef (Typ(..), Work(..))
import InferLazyMF (chk, mono, chkAndShow)
import qualified InferSimple as InferS (Typ(..), Work(..), chk)
import Test.QuickCheck.Gen (elements)
import System.Posix.ByteString (seekDirStream)
import System.Random.Stateful (RandomGen(genWord32))

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

-- getRandomElement :: RandomGen g => g -> [a] -> (a, g)
-- getRandomElement gen ls =
--     let (idx, nextGen) = randomR (0, length ls) gen in
--         (ls !! idx, nextGen)

probs :: [Float]
probs = [0.2, 0.2, 0.2, 0.2, 0.2]

cumProbs :: [Float]
cumProbs = 
    let cumProbs = 0.0 : scanl1 (+) probs in
        if abs(1.0 - last cumProbs) < 0.01 then cumProbs else error "Error: all probs should sum to 1.0!"

-- abstractHelper :: RandomGen g => g -> Typ -> [Typ] -> (Typ, g)
-- abstractHelper gen TInt typLs =
--     let (x, nextGen) = random gen in
--         if (x :: Float) < 0.5 then (TInt, nextGen) else
--             let (t, nextGen') = getRandomElement nextGen typLs
--                 in (t, nextGen')
-- abstractHelper gen TBool typLs =
--     let (x, nextGen) = random gen in
--         if (x :: Float) < 0.5 then (TBool, nextGen) else
--             let (t, nextGen') = getRandomElement nextGen typLs
--                 in (t, nextGen')
-- abstractHelper gen (TArrow t1 t2) typLs =
--     let (x, nextGen) = random gen in
--         if | (x :: Float) > head cumProbs && (x :: Float) > cumProbs !! 1->
--                 let (t1', nextGen) = abstractHelper gen t1 typLs in
--                     let (t2', nextGen') = abstractHelper nextGen t2 typLs in
--                         (TArrow t1' t2', nextGen')
--            | (x :: Float) > cumProbs !! 1 && (x :: Float) > cumProbs !! 2 ->
--                let (tvar, nextGen) = getRandomElement gen typLs in
--                    let (t2', nextGen') = abstractHelper nextGen t2 typLs in
--                     (TArrow tvar t2', nextGen')
--            | (x :: Float) > cumProbs !! 1 && (x :: Float) > cumProbs !! 2 ->
--                let (tvar, nextGen) = getRandomElement gen typLs in
--                    let (t1', nextGen') = abstractHelper nextGen t1 typLs in
--                     (TArrow t1' tvar, nextGen')
--            | (x :: Float) > cumProbs !! 2 && (x :: Float) > cumProbs !! 3 ->
--                let (tvar1, nextGen) = getRandomElement gen typLs in
--                    let (tvar2, nextGen') = getRandomElement nextGen typLs in 
--                        (TArrow tvar1 tvar2, gen)
--            | (x :: Float) > cumProbs !! 3 && (x :: Float) > cumProbs !! 4 ->
--                 (TForall $ \x -> TArrow (fst $ abstractHelper nextGen t1 (x:typLs)) t2, nextGen)
--            | (x :: Float) > cumProbs !! 4 && (x :: Float) > cumProbs !! 5 ->
--                 (TForall $ \x -> TArrow t1 (fst $ abstractHelper nextGen t2 (x:typLs)), nextGen)
--            | (x :: Float) > 0.5 -> (TArrow t1 t2, gen)
--            | otherwise -> (TArrow t1 t2, gen)
-- abstractHelper gen (TVar _) typLs = error "Bug: Wellformed type should not contain var!"
-- abstractHelper gen (TForall tt) typLs = (TForall (\x -> fst $ abstractHelper gen (tt x) (x:typLs)), gen)

-- abstract :: Typ -> Int -> Typ
-- abstract typ seed = fst $ abstractHelper (mkStdGen seed) typ []


getRandomElement :: Int -> [a] -> (a, Int)
getRandomElement seed ls =
    (ls !! idx, nextSeed) 
    where 
        gen = mkStdGen seed
        idx = fst $ randomR (0, length ls - 1) gen 
        nextSeed = fromIntegral $ fst $ genWord32 gen

getRandomFloat :: Int -> (Float, Int)
getRandomFloat seed  =
    (x, nextSeed) 
    where 
        gen = mkStdGen seed
        x = fst $ random gen
        nextSeed = fromIntegral $ fst $ genWord32 gen

getSeedFromTime :: Int -> Int
getSeedFromTime _ = round $ 1e6 * unsafePerformIO (getCurrentTime <&> (fromRational . toRational . utctDayTime))

getSeedsFromTime :: [Int]
getSeedsFromTime = getSeedsFromTimeHelper 0
    where getSeedsFromTimeHelper n = getSeedFromTime n : getSeedsFromTimeHelper (n + 1)

abstractHelper :: Int -> Typ -> [Typ] -> (Typ, Int)
abstractHelper seed TInt typLs =
    if null typLs then 
        (TInt, seed)
    else
        let (x :: Float, nextSeed) = getRandomFloat seed in
            if x < 0.5 
                then (TInt, nextSeed) 
                else getRandomElement nextSeed typLs
abstractHelper seed TBool typLs =
    if null typLs then 
        (TBool, seed)
    else
        let (x :: Float, nextSeed) = getRandomFloat seed in
            if x < 0.5 
                then (TBool, nextSeed) 
                else getRandomElement nextSeed typLs
abstractHelper seed (TArrow t1 t2) typLs =
    let (x :: Float, nextSeed) = getRandomFloat seed in
        if | x > head cumProbs && x < cumProbs !! 1->
                let (polyt1, nextSeed') = abstractHelper nextSeed t1 typLs 
                    (polyt2, nextSeed'') = abstractHelper nextSeed' t2 typLs in
                        (TArrow polyt1 polyt2, nextSeed'')
            | x > cumProbs !! 1 && x < cumProbs !! 2 ->
                (TForall $ \x -> 
                    let (polyt1, nextSeed') = abstractHelper nextSeed t1 (x:typLs) 
                        (polyt2, _) = abstractHelper nextSeed' t1 (x:typLs) in 
                    TArrow polyt1 polyt2,  getSeedFromTime 0)
            | x > cumProbs !! 2 && x < cumProbs !! 3 ->
                 (TForall $ \x -> x, nextSeed)
            | x > cumProbs !! 3 && x < cumProbs !! 4 -> getRandomElement seed typLs
            | otherwise -> (TArrow t1 t2, seed)
abstractHelper seed t typLs = error $ "Bug: Wellformed mono type should not contain " ++ show t ++ "!"


abstract :: Typ -> Int -> Typ
abstract typ seed = fst $ abstractHelper seed typ []


-- https://www.seas.upenn.edu/~cis552/12fa/lectures/stub/QuickCheck.html
-- https://stackoverflow.com/questions/17615138/haskell-quickcheck-to-generate-and-test-rose-trees
-- https://www.cse.chalmers.se/~rjmh/QuickCheck/manual_body.html
monoTypGen :: Gen Typ
monoTypGen = sized monoNTypGen
    where monoNTypGen 0 = elements [TBool, TInt]
          monoNTypGen n = oneof [liftM2 TArrow (monoNTypGen (n - 1)) (monoNTypGen (n - 1)),
                                 elements [TBool, TInt]
                                ]
polyTypGen :: Typ -> Gen Typ
polyTypGen = polyTypGenHelper []
    where
        polyTypGenHelper typLs TInt =
            do
                t <- elements typLs
                elements [TInt, t]
        polyTypGenHelper typLs TBool =
            do
                t <- elements typLs
                elements [TBool, t]
        polyTypGenHelper typLs (TArrow t1 t2) =
            if null typLs then
                do
                    polyt1 <- polyTypGenHelper typLs t1
                    polyt2 <- polyTypGenHelper typLs t2
                    let ta = TArrow polyt1 polyt2
                    elements [ta]
            else
                do
                    tvar1 <- elements typLs
                    tvar2 <- elements typLs
                    polyt1 <- polyTypGenHelper typLs t1
                    polyt2 <- polyTypGenHelper typLs t2
                    let ta = TArrow polyt1 polyt2
                    let tb = TArrow tvar1 polyt2
                    let tc = TArrow polyt1 tvar2
                    let td = TArrow tvar1 tvar2
                    let te = TForall (\x -> TArrow x x)
                    let tf = \x -> polyTypGenHelper (x:typLs) t1
                    elements [ta, tb, tc, td, te]
        polyTypGenHelper typLs t = error $ "Bug: Wellformed mono type should not contain " ++ show t ++ "!"


instance Arbitrary Typ where
    arbitrary = monoTypGen

instance {-# OVERLAPPING #-} Arbitrary [Work] where
    arbitrary = do
                   leftTyp <- arbitrary
                   rightTyp <- arbitrary
                   seed <- arbitrary
                   frequency
                         [(2, return [Sub leftTyp (abstract leftTyp seed)]),
                          (1, return [Sub leftTyp rightTyp])]

test1 = chkAndShow [Sub (TArrow TInt (TArrow TInt TBool )) (TForall (\t -> (TArrow t (TArrow TInt t))))]

testSample = take 10 (randomRs ('a', 'z') (mkStdGen 10))
