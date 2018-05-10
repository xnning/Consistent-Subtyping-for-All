module Language.HigherRank.Main (main) where

import System.Console.Haskeline

import Language.HigherRank.Parse
import Language.HigherRank.Print
import Language.HigherRank.Typecheck

fromEither :: Either a a -> a
fromEither (Left x) = x
fromEither (Right x) = x

repl :: (String -> String) -> IO ()
repl f = runInputT defaultSettings loop
  where
    loop =
      getInputLine "> " >>= \case
        Nothing -> return ()
        Just l -> outputStrLn (f l) >> loop

main :: IO ()
main =
  repl $ \input ->
    fromEither $ do
      e <- parseExpr input
      t <- runInfer e
      return $ "Typing result of " ++ pprint e ++ ":\n" ++ pprint t
