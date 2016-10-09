import Bootstrap
import Environment
import Types

main :: IO ()
main = do
  env <- initEnv
  runKLC bootstrap
       (\_ _ -> return ())
       (\_ _ -> return ())
       env       
