{-# LANGUAGE TypeFamilies         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

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
instance SOP.Generic P.Inline
instance SOP.Generic P.Format
instance SOP.Generic P.QuoteType
instance SOP.Generic P.ListNumberStyle
instance SOP.Generic P.ListNumberDelim
instance SOP.Generic P.Alignment
instance SOP.Generic P.MathType
instance SOP.Generic P.Citation
instance SOP.Generic P.CitationMode

instance Diff P.Pandoc
instance Diff P.Meta
instance Diff P.MetaValue
instance Diff P.Block
instance Diff P.Inline
instance Diff P.Format
instance Diff P.QuoteType
instance Diff P.ListNumberStyle
instance Diff P.ListNumberDelim
instance Diff P.Alignment
instance Diff P.MathType
instance Diff P.Citation
instance Diff P.CitationMode

loadDoc :: FilePath -> IO P.Pandoc
loadDoc = P.runIOorExplode . P.readMarkdown def <=< T.readFile

printDoc :: P.Pandoc -> T.Text
printDoc = either undefined id . P.runPure . P.writeMarkdown def

main :: IO ()
main = do
    p1:p2:p3:_ <- traverse loadDoc =<< getArgs
    print p1
    case merge p1 p2 p3 of
      Incompatible -> putStrLn "no merge"
      Conflict p   -> putStrLn "conflict" >> T.putStrLn (printDoc p)
      NoConflict p -> putStrLn "no conflict" >> T.putStrLn (printDoc p)
