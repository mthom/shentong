import Shentong.Bootstrap
import Shentong.Environment
import Shentong.Types

main :: IO ()
main = do
  env <- initEnv
  runKLC bootstrap
       (\_ _ -> return ())
       (\_ _ -> return ())
       env       
