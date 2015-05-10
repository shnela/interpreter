
data Err a = Ok a | Bad String
  deriving (Read, Show, Eq, Ord)

instance Monad Err where
  return      = Ok
  fail        = Bad
  Ok a  >>= f = f a
  Bad s >>= f = Bad s

main :: IO ()
main = do

run :: String -> IO ()
run s = let ts = myLexer s in case pProg ts of
           Bad msg   -> do putStrLn msg;
           Ok p   -> do putStrLn $show (interpret p);
                        return ();
