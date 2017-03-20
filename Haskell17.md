Scrap your proofs: a generic approach to refinement reflection
---------------------------------------------------------------

- Idea: 
  - Let `v` be a dictionary like data type with property-methods. 
  - The ADT `a` satisifies the properties of `v` if the value `v a` exists. 
  - The function `vIso`, given an auto-derived isomorphic proof from `a` to `b` translates the proofs `v a` to `v b` 

```
vIso :: (Iso a b) -> v a -> v b`
```

- Automatic Deriviation of Isomorphisms via Template Haskell @rgscott 
- Applications
 - Example 1 `v := VerifiedEq`, `a := Int`, `b := MyInt`
 - Example 2 `v := VerifiedNum`, `a := Int`, `b := MyInt`
 - Example 3 `v := VerifiedNum`, `a := Nat`, `b := Peano`
 - Example 4 `v := VerifiedApplicative`, `a := List`, `b := ???`

