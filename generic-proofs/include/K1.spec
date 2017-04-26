module spec K1 where

assume K1   :: c:c -> {v:K1 i c p | v == K1 c &&  unK1 v == c && select_K1_1 v == c }
assume unK1 :: k:K1 i c p -> {v:c | v == unK1 k && v == select_K1_1 k && K1 v == k }

measure select_K1_1 :: K1 i c p -> c
measure unK1        :: K1 i c p -> c
