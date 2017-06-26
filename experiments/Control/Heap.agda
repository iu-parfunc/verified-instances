{-# OPTIONS --type-in-type #-}

module Control.Heap where

open import Prelude
open import Builtin.Float

IVar : Set
IVar = Int

Val : Set
Val = Float

data Heap : Set where
  ε : Heap
  _↦̸,_ : (ix : IVar) → (h : Heap) → Heap
  _↦_,_ : (ix : IVar) → (v : Val) → (h : Heap) → Heap

toList : Heap → List (IVar × Maybe Val)
toList ε = []
toList (ix ↦̸, h) = (ix , nothing) ∷ toList h
toList (ix ↦ v , h) = (ix , just v) ∷ toList h

fromList : List (IVar × Maybe Val) → Heap
fromList [] = ε
fromList ((ix , nothing) ∷ ts) = ix ↦̸, fromList ts
fromList ((ix ,  just v) ∷ ts) = ix ↦ v , fromList ts
