module spec GenericProofs.Iso where

assume id :: x:a -> {y:a | y == x}
assume (.) :: f:(b -> c) -> g:(a -> b) -> x:a -> {y:c | y == f (g x)}

assume identity :: x:a -> {y:a | y == x}
assume compose :: f:(b -> c) -> g:(a -> b) -> x:a -> {y:c | y == f (g x)}
