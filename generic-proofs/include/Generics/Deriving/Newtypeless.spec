module spec Generics.Deriving.Newtypeless where

assume K1   :: c:c -> {v:K1 i c p | v == K1 c &&  unK1 v == c && select_K1_1 v == c }
assume unK1 :: k:K1 i c p -> {v:c | v == unK1 k && v == select_K1_1 k && K1 v == k }

measure select_K1_1 :: K1 i c p -> c
measure unK1        :: K1 i c p -> c

assume Product :: a:f p -> b:g p -> {v:Product f g p | v == Product a b && select_Product_1 v == a && select_Product_2 v == b }

measure select_Product_1 :: Product f g p -> (f p)
measure select_Product_2 :: Product f g p -> (g p)
