import Test.Hspec
import Alg (run)
import System.Directory
import System.FilePath.Posix

main :: IO ()
main = do
  files <- listDirectory "examples/our_examples"
  hspec $ do
    describe "our_examples" $
      mapM_ (\file -> it file (run ("examples/our_examples/" ++ file) False)) [f | f <- files, ".e" `elem` splitExtension f]
