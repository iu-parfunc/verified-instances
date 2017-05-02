module GenericProofs.TH where

import Generics.Deriving.Newtypeless.TH
import Language.Haskell.TH

deriveIso :: Name -> Q [Dec]
deriveIso n = do
  genericInstance <- deriveAll0 n
  return genericInstance
