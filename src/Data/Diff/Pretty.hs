
module Data.Diff.Pretty (
    ppDel
  , ppAdd
  , ppMod
  , ppNoChange
  ) where

import           Data.Semigroup
import qualified Text.PrettyPrint.ANSI.Leijen as PP

ppDel :: PP.Doc -> PP.Doc
ppDel x = PP.red (PP.char '-') <> PP.align x

ppAdd :: PP.Doc -> PP.Doc
ppAdd x = PP.green (PP.char '+') <> PP.align x

ppMod :: PP.Doc -> PP.Doc
ppMod x = PP.yellow (PP.char '~') <> PP.align x

ppNoChange :: PP.Doc
ppNoChange = PP.text "<no change>"
