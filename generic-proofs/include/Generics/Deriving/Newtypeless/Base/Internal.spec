module spec Generics.Deriving.Newtypeless.Base.Internal where

data M1 i c f p = M1 { unM1 :: (f p) }

data K1 i c p = K1 { unK1 :: c }

data Par1 p = Par1 { unPar1 :: p }

data Rec1 f p = Rec1 { unRec1 :: (f p) }

data Sum f g p = L1 { l1 :: (f p) } | R1 { r1 :: (g p) }

data Product f g p = Product { prd1 :: (f p), prd2 :: (g p) }

data Comp1 f g p = Comp1 { unComp1 :: (f (g p)) }
