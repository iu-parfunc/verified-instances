module spec Generics.Deriving.Newtypeless where

assume K1   :: c:c -> {v:K1 i c p | v == K1 c &&  unK1 v == c && select_K1_1 v == c }
assume unK1 :: k:K1 i c p -> {v:c | v == unK1 k && v == select_K1_1 k && K1 v == k }

measure select_K1_1 :: K1 i c p -> c
measure unK1        :: K1 i c p -> c

assume Product :: a:f p -> b:g p -> {v:Product f g p | v == Product a b && select_Product_1 v == a && select_Product_2 v == b }

measure select_Product_1 :: Product f g p -> (f p)
measure select_Product_2 :: Product f g p -> (g p)

assume L1 :: a:(f p) -> {v:Sum f g p | v == L1 a && select_L1_1 v == a && is_L1 v && not (is_R1 v)}
assume R1 :: b:(g p) -> {v:Sum f g p | v == R1 b && select_R1_1 v == b && not (is_L1 v) && is_R1 v }

measure select_L1_1 :: Sum f g p -> (f p)
measure select_R1_1 :: Sum f g p -> (g p)

measure is_L1 :: Sum f g p -> Bool
measure is_R1 :: Sum f g p -> Bool
