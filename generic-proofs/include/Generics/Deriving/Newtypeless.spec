module spec Generics.Deriving.Newtypeless where

assume U1 :: {v:U1 p | v == U1 }

assume M1   :: a:(f p) -> {v:M1 i c f p | v == M1 a && unM1 v == a && select_M1_1 v == a }
assume unM1 :: m:M1 i c f p -> {v:(f p) | v == unM1 m && v == select_M1_1 m && M1 v == m }

measure select_M1_1 :: M1 i c f p -> (f p)
measure unM1        :: M1 i c f p -> (f p)

assume K1   :: c:c -> {v:K1 i c p | v == K1 c &&  unK1 v == c && select_K1_1 v == c }
assume unK1 :: k:K1 i c p -> {v:c | v == unK1 k && v == select_K1_1 k && K1 v == k }

measure select_K1_1 :: K1 i c p -> c
measure unK1        :: K1 i c p -> c

assume Par1   :: a:p -> {v:Par1 p | v == Par1 a && unPar1 v == a && select_Par1_1 v == a }
assume unPar1 :: p:Par1 p -> {v:p | v == unPar1 p && v == select_Par1_1 p && Par1 v == p }

measure select_Par1_1 :: Par1 p -> p
measure unPar1        :: Par1 p -> p

assume Product :: a:f p -> b:g p -> {v:Product f g p | v == Product a b && select_Product_1 v == a && select_Product_2 v == b }

measure select_Product_1 :: Product f g p -> (f p)
measure select_Product_2 :: Product f g p -> (g p)

assume L1 :: a:(f p) -> {v:Sum f g p | v == L1 a && select_L1_1 v == a && is_L1 v && not (is_R1 v)}
assume R1 :: b:(g p) -> {v:Sum f g p | v == R1 b && select_R1_1 v == b && not (is_L1 v) && is_R1 v }

measure select_L1_1 :: Sum f g p -> (f p)
measure select_R1_1 :: Sum f g p -> (g p)

measure is_L1 :: Sum f g p -> Bool
measure is_R1 :: Sum f g p -> Bool
