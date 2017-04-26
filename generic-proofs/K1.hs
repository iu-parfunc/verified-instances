-- K1.hs
module K1 where

data K1 i c p = K1 { unK1 :: c }
type Rec0  = K1 R
data R
