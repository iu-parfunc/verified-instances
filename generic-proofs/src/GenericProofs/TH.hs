{-# LANGUAGE TemplateHaskell #-}
module GenericProofs.TH where

import Control.Lens ((^..))
import GenericProofs.Iso (Iso(Iso))
import Generics.Deriving.Newtypeless
import Generics.Deriving.Newtypeless.TH
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import Language.Haskell.TH.Lens (typeVars)

deriveIso :: String -- ^ Name of the proof that @to . from = id@
          -> String -- ^ Name of the proof that @from . to = id@
          -> String -- ^ Name of the 'Iso'
          -> Name   -- ^ Name of the datatype
          -> Q [Dec]
deriveIso tof fot iso n = do
  metaDecs        <- deriveMeta n
  genericInstance <- deriveRepresentable0 n
  fromExp         <- makeFrom0 n
  toExp           <- makeTo0 n
  x               <- newName "x"
  z               <- newName "z"
  fromInternal    <- newName "fromInternal"
  toInternal      <- newName "toInternal"

  let tofN, fotN, isoN :: Name
      tofN = mkName tof
      fotN = mkName fot
      isoN = mkName iso

      -- Technically, we could also retrieve this information from
      -- deriveRepresentable0, but this is a smidge more convenient.
      fotPatsAndExps, tofPatsAndExps :: [(Pat,Exp)]
      fotPatsAndExps = case toExp of
                         LamE [VarP _] (CaseE (VarE _) [Match (ConP _ [VarP _]) (NormalB (CaseE (VarE _) matches)) []]) ->
                           map (\(Match pat (NormalB expr) []) -> (ConP 'M1 [pat], expr)) matches
                         _ -> error $ "deriveIso: fotPatsAndExps\n" ++ pprint toExp
      tofPatsAndExps = case fromExp of
                         LamE [VarP _] (CaseE (VarE _) [Match (VarP _) (NormalB (AppE (ConE _) (CaseE (VarE _) matches))) []]) ->
                           map (\(Match pat (NormalB expr) []) -> (pat, ConE 'M1 `AppE` expr)) matches
                         _ -> error $ "deriveIso: tofPatsAndExps\n" ++ pprint fromExp

      dataType, repType :: Q Type
      dataType = case genericInstance of
                   [InstanceD _ (AppT _ t) _] -> return t
                   _ -> fail "deriveIso: dataType"
      repType = [t| Rep $(dataType) $(varT x) |]

      isoDecsQ :: Q [Dec]
      isoDecsQ = do
        ty <- repType
        sequence [ sigD isoN $ forallT (map PlainTV (ty^..typeVars)) (return []) [t| Iso $(dataType) $(repType) |]
                 , funD isoN [clause [] (normalB [| Iso from to $(varE fotN) $(varE tofN) |]) []]
                 ]

      internalDecsQ :: Name -> Name -> Q Type -> Q Type -> Q [Dec]
      internalDecsQ internalN funN ty1 ty2 = do
        rt <- repType
        sequence
          [ sigD internalN $ forallT (map PlainTV (rt^..typeVars)) (return []) [t| $(ty1) -> $(ty2) |]
          , funD internalN [clause [] (normalB (varE funN)) []]
          ]

      fromInternalDecsQ, toInternalDecsQ :: Q [Dec]
      fromInternalDecsQ = internalDecsQ fromInternal 'from dataType repType
      toInternalDecsQ   = internalDecsQ toInternal   'to   repType  dataType

      proofDecsQ :: Name -> Name -> Name -> Q Type -> [(Pat,Exp)] -> Q [Dec]
      proofDecsQ fun1oFun2N fun1N fun2N qTy patsAndExps = do
        ty <- qTy
        sequence
          [ sigD fun1oFun2N $ forallT (map PlainTV (ty^..typeVars)) (return []) [t| $(qTy) -> Proof |]
          , funD fun1oFun2N $ map (\(pat,expr) -> clause [asP z $ return pat]
                                                         (normalB [|     $(varE fun1N) ($(varE fun2N) $(varE z))
                                                                     ==. $(varE fun1N) $(return expr)
                                                                     ==. $(varE z)
                                                                     *** QED
                                                                   |]) [])
                              patsAndExps
          ]

      fotDecsQ, tofDecsQ :: Q [Dec]
      fotDecsQ = proofDecsQ fotN fromInternal toInternal repType  fotPatsAndExps
      tofDecsQ = proofDecsQ tofN toInternal fromInternal dataType tofPatsAndExps

  fromInternalDecs <- fromInternalDecsQ
  toInternalDecs   <- toInternalDecsQ
  fotDecs          <- fotDecsQ
  tofDecs          <- tofDecsQ
  isoDecs          <- isoDecsQ
  return $ concat [ metaDecs
                  , genericInstance
                  , fromInternalDecs
                  , toInternalDecs
                  , fotDecs
                  , tofDecs
                  , isoDecs
                  ]
