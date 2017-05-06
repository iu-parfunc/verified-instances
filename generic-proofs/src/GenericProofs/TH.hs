{-# LANGUAGE TemplateHaskell #-}
module GenericProofs.TH where

import Control.Lens ((^..))
import Data.Foldable (foldl')
import GenericProofs.Iso (Iso(Iso))
import Generics.Deriving.Newtypeless.Base.Internal
import Generics.Deriving.Newtypeless.TH
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import Language.Haskell.TH.Lens (typeVars)

deriveIso :: String -- ^ Name of the representation type synonym
          -> String -- ^ Name of the @to@ function
          -> String -- ^ Name of the @from@ function
          -> String -- ^ Name of the proof that @to . from = id@
          -> String -- ^ Name of the proof that @from . to = id@
          -> String -- ^ Name of the 'Iso'
          -> Name   -- ^ Name of the datatype
          -> Q [Dec]
deriveIso rep toFun fromFun tof fot iso dataN = do
  metaDecs        <- deriveMeta dataN
  repTypeSyn      <- deriveRep0 dataN
  genericInstance <- deriveRepresentable0 dataN
  fromExp         <- makeFrom0 dataN
  toExp           <- makeTo0 dataN
  x               <- newName "x"
  z               <- newName "z"

  let repN, fromN, toN, tofN, fotN, isoN :: Name
      repN  = mkName rep
      fromN = mkName fromFun
      toN   = mkName toFun
      tofN  = mkName tof
      fotN  = mkName fot
      isoN  = mkName iso

      -- Technically, we could also retrieve this information from
      -- deriveRepresentable0, but this is a smidge more convenient.
      toPatsAndExps, fromPatsAndExps :: [(Pat,Exp)]
      toPatsAndExps = case toExp of
                         LamE [VarP _] (CaseE (VarE _) [Match (ConP _ [VarP _]) (NormalB (CaseE (VarE _) matches)) []]) ->
                           map (\(Match pat (NormalB expr) []) -> (ConP 'M1 [pat], expr)) matches
                         _ -> error $ "deriveIso: fotPatsAndExps\n" ++ pprint toExp
      fromPatsAndExps = case fromExp of
                         LamE [VarP _] (CaseE (VarE _) [Match (VarP _) (NormalB (AppE (ConE _) (CaseE (VarE _) matches))) []]) ->
                           map (\(Match pat (NormalB expr) []) -> (pat, ConE 'M1 `AppE` expr)) matches
                         _ -> error $ "deriveIso: tofPatsAndExps\n" ++ pprint fromExp

      tvbToTyVar :: TyVarBndr -> Type
      tvbToTyVar (PlainTV n)    = VarT n
      tvbToTyVar (KindedTV n k) = SigT (VarT n) k

      -- Construct a type via curried application.
      applyTyToTys :: Type -> [Type] -> Type
      applyTyToTys = foldl' AppT

      repTypeTyVars :: [Type]
      repTypeSyn'   :: [Dec]
      (repTypeTyVars, repTypeSyn') = case repTypeSyn of
                                       [TySynD _ tvbs ty] -> (map tvbToTyVar tvbs, [TySynD repN tvbs ty])
                                       _ -> error "deriveIso: repTypeSyn'"

      dataType, repType :: Q Type
      dataType = case genericInstance of
                   [InstanceD _ _ (AppT _ t) _] -> return t
                   _ -> fail "deriveIso: dataType"
      repType = return $ applyTyToTys (ConT repN) $ repTypeTyVars ++ [VarT x]

      mkForallT :: Type -> Q Type -> Q Type
      mkForallT ty qBodyTy = forallT (map PlainTV (ty^..typeVars)) (return []) qBodyTy

      isoDecsQ :: Q [Dec]
      isoDecsQ = do
        ty <- repType
        sequence [ sigD isoN $ mkForallT ty [t| Iso $(dataType) $(repType) |]
                 , funD isoN [clause [] (normalB [| Iso $(varE fromN) $(varE toN)
                                                        $(varE fotN) $(varE tofN) |])
                                                 []]
                 ]

      fromToDecsQ :: Name -> Q Type -> Q Type -> [(Pat,Exp)] -> Q [Dec]
      fromToDecsQ fromToN ty1 ty2 patsAndExps = do
        rt <- repType
        sequence
          [ sigD fromToN $ mkForallT rt [t| $(ty1) -> $(ty2) |]
          , funD fromToN $ map (\(pat,expr) -> clause [return pat] (normalB (return expr)) [])
                               patsAndExps
          ]

      fromDecsQ, toDecsQ :: Q [Dec]
      fromDecsQ = fromToDecsQ fromN dataType repType  fromPatsAndExps
      toDecsQ   = fromToDecsQ toN   repType  dataType toPatsAndExps

      proofDecsQ :: Name -> Name -> Name -> Q Type -> [(Pat,Exp)] -> Q [Dec]
      proofDecsQ fun1oFun2N fun1N fun2N qTy patsAndExps = do
        ty <- qTy
        sequence
          [ sigD fun1oFun2N $ mkForallT ty [t| $(qTy) -> Proof |]
          , funD fun1oFun2N $ map (\(pat,expr) -> clause [asP z $ return pat]
                                                         (normalB [|     $(varE fun1N) ($(varE fun2N) $(varE z))
                                                                     ==. $(varE fun1N) $(return expr)
                                                                     ==. $(varE z)
                                                                     *** QED
                                                                   |]) [])
                                  patsAndExps
          ]

      fotDecsQ, tofDecsQ :: Q [Dec]
      fotDecsQ = proofDecsQ fotN fromN toN repType  toPatsAndExps
      tofDecsQ = proofDecsQ tofN toN fromN dataType fromPatsAndExps

  fromDecs <- fromDecsQ
  toDecs   <- toDecsQ
  fotDecs  <- fotDecsQ
  tofDecs  <- tofDecsQ
  isoDecs  <- isoDecsQ
  return $ concat [ metaDecs
                  , repTypeSyn'
                  , fromDecs
                  , toDecs
                  , fotDecs
                  , tofDecs
                  , isoDecs
                  ]
