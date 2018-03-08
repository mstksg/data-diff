
{-# LANGUAGE TypeFamilies #-}

import           Control.Monad
import           Data.Default
import           Data.Diff
import           System.Environment
import qualified Data.Text          as T
import qualified Data.Text.IO       as T
import qualified Generics.SOP       as SOP
import qualified Text.Pandoc        as P

instance SOP.Generic P.Pandoc
instance SOP.Generic P.Meta
instance SOP.Generic P.MetaValue
instance SOP.Generic P.Block

-- instance Diff P.Pandoc where
-- instance Diff P.Meta where
-- instance Diff P.MetaValue where
-- instance Diff P.Block where

loadDoc :: FilePath -> IO P.Pandoc
loadDoc = P.runIOorExplode . P.readMarkdown def <=< T.readFile

printDoc :: P.Pandoc -> T.Text
printDoc = either undefined id . P.runPure . P.writeMarkdown def

main :: IO ()
main = do
    p1:p2:p3:_ <- traverse loadDoc =<< getArgs
    -- case merge p1 p2 p3 of
    case undefined p1 p2 p3 of
      Incompatible -> putStrLn "no merge"
      Conflict p   -> putStrLn "conflict" >> T.putStrLn (printDoc p)
      NoConflict p -> putStrLn "no conflict" >> T.putStrLn (printDoc p)

