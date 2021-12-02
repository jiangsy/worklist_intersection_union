module TestInfer where

-- https://stackoverflow.com/questions/35589705/quickcheck-for-runtime-errors
import System.IO.Unsafe

import qualified InferLazySimple as InferLS
import qualified Old.InferSimple as InferS

adaptWork :: InferLS.Work -> InferS.Work
adaptWork = undefined

inferEqProp :: [InferLS.Work] -> Bool 
inferEqProp wl = unsafePerformIO (InferLS.chk' wl) == unsafePerformIO (InferS.chk' (map adaptWork wl))