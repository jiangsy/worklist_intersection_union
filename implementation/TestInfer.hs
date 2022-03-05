{-# LANGUAGE FlexibleInstances, MultiWayIf, ScopedTypeVariables #-}
module TestInfer where

import Control.Monad (liftM,liftM2,liftM3)
import Data.Functor
import Data.Time.Clock ( UTCTime(utctDayTime), getCurrentTime )
import Test.QuickCheck
    ( chooseInt,
      elements,
      frequency,
      oneof,
      sized,
      verboseCheck,
      Arbitrary(arbitrary),
      Gen )
import Test.QuickCheck.Property (succeeded, failed, reason, Result)
import System.IO.Unsafe
import System.Random (StdGen, mkStdGen, random, randomR, randomRs, RandomGen)
import System.Random.Stateful (RandomGen(genWord32))


import LazyDef (Typ(..), Work(..))
import InferLazyMB (chk, mono, chkAndShow, checkAndShow)
import TestCase
import qualified InferSimple as InferS (Typ(..), Work(..), chk, chkAndShow, checkAndShow)

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


inferEqProp :: [Work] -> Test.QuickCheck.Property.Result
inferEqProp wl =
  if chk wl == InferS.chk wl'
    then succeeded
    else failed { reason = reason' }
   where
      wl' = map adaptWorkLStoS wl
      full_chk_res = checkAndShow 0 wl 
      full_chk_res' = InferS.checkAndShow 0 wl'
      last_line = last (lines full_chk_res)
      last_line' = last (lines full_chk_res')
      reason' = full_chk_res ++ "\n" ++ full_chk_res' ++ "\n"

-- getRandomElement :: RandomGen g => g -> [a] -> (a, g)
-- getRandomElement gen ls =
--     let (idx, nextGen) = randomR (0, length ls) gen in
--         (ls !! idx, nextGen)

probs :: [Float]
probs = [0.3, 0.3, 0.3, 0.1]

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
maxRandomSeedUsed :: Typ -> Int
maxRandomSeedUsed TInt           = 2
maxRandomSeedUsed TBool          = 2
maxRandomSeedUsed (TArrow t1 t2) = 3 + maxRandomSeedUsed t1 + maxRandomSeedUsed t2
maxRandomSeedUsed _              = error "Bug: maxRandomSeedUsed should be called on mono type only!"


getNewSeed :: Int -> Int -> Int 
getNewSeed seed n = getNewSeedHelper gen n
    where gen = mkStdGen seed
          getNewSeedHelper gen 0 = fromIntegral $ fst $ genWord32 gen
          getNewSeedHelper gen n = getNewSeedHelper (snd $ genWord32 gen) (n-1)
    

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

-- avoid call-by-need optimization, otherwise calling getSeedFromTime will get the same result
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
            if x < 0.2
                then (TInt, nextSeed) 
                else getRandomElement nextSeed typLs
abstractHelper seed TBool typLs =
    if null typLs then 
        (TBool, seed)
    else
        let (x :: Float, nextSeed) = getRandomFloat seed in
            if x < 0.2
                then (TBool, nextSeed) 
                else getRandomElement nextSeed typLs
abstractHelper seed t@(TArrow t1 t2) typLs =
    if null typLs then 
        let (x :: Float, nextSeed) = getRandomFloat seed in
            if | x < 0.2 ->
                    let (polyt1, nextSeed') = abstractHelper nextSeed t1 typLs 
                        (polyt2, nextSeed'') = abstractHelper nextSeed' t2 typLs in
                            (TArrow polyt1 polyt2, nextSeed'')
                | x >= 0.2 && x < 0.95 ->
                    (TForall $ \x -> 
                        let (polyt1, nextSeed') = abstractHelper nextSeed t1 (x:typLs) 
                            (polyt2, _) = abstractHelper nextSeed' t2 (x:typLs) in 
                        TArrow polyt1 polyt2, getNewSeed seed (maxRandomSeedUsed t))
                | otherwise -> (TArrow t1 t2, seed)
    else
        let (x :: Float, nextSeed) = getRandomFloat seed in
            if | x < 0.3 ->
                    let (polyt1, nextSeed') = abstractHelper nextSeed t1 typLs 
                        (polyt2, nextSeed'') = abstractHelper nextSeed' t2 typLs in
                            (TArrow polyt1 polyt2, nextSeed'')
                | x >= 0.3 && x < 0.6 ->
                    (TForall $ \x -> 
                        let (polyt1, nextSeed') = abstractHelper nextSeed t1 (x:typLs) 
                            (polyt2, _) = abstractHelper nextSeed' t2 (x:typLs) in 
                        TArrow polyt1 polyt2, getNewSeed seed (maxRandomSeedUsed t))
                | x >= 0.6 && x < 0.9 -> 
                    getRandomElement seed typLs
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
          monoNTypGen n = frequency [(4, liftM2 TArrow (monoNTypGen (n - 1)) (monoNTypGen (n - 1))),
                                     (1, elements [TBool, TInt])]

monoNTypGen :: Int -> Gen Typ
monoNTypGen 0 = elements [TBool, TInt]
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
    arbitrary = 
        do 
            n <- frequency [    
                    (1, chooseInt (1, 2)),
                    (7, chooseInt (3, 5)),
                    (2, chooseInt (6, 10))]
            monoNTypGen n

instance {-# OVERLAPPING #-} Arbitrary [Work] where
    arbitrary = do
                   t1 <- arbitrary
                   t2 <- arbitrary
                   seed1 <- arbitrary
                   frequency
                         [(1, return [Sub (abstract t1 seed1) t1]),
                          (2, return [Sub (abstract t1 seed1) (abstract t1 (seed1+1))]),
                          (2, return [Sub (abstract t1 seed1) (abstract t2 (seed1+1))])]

test1 = chkAndShow [Sub (TArrow TInt (TArrow TInt TBool )) (TForall (\t -> (TArrow t (TArrow TInt t))))]

wl = [Sub t12 t13]
wl' = map adaptWorkLStoS wl 
main = verboseCheck inferEqProp

wl2 = [Sub t14 t15]
wl2' = map adaptWorkLStoS wl2


wl3 = [Sub t16 t17]
wl3' = map adaptWorkLStoS wl3

wl4 = [Sub t10 t11]
wl4' = map adaptWorkLStoS wl4

wl5 = [Sub t18 t19]
wl5' = map adaptWorkLStoS wl5

wl6 = [Sub t20 t21]
wl6' = map adaptWorkLStoS wl6