import R1Z.PV_RDB2_CBL_LibraryShapes
namespace R1Z.PV_CBL_GenericArrayFlatten
open PV_CBL_LibraryShapes
set_option autoImplicit false

def even {T U : Type} (flatten : U→List T) (v : Even T U) : List T :=
  flatten v.parent1 ++ flatten v.parent2

def odd {T U : Type} (flatten : U→List T) (v : Odd T U) : List T :=
  flatten v.parent1 ++ flatten v.parent2 ++ [v.data]

theorem even_length {T U : Type} (flatten : U→List T) (k : Nat)
    (h : ∀ u, (flatten u).length=k) (v : Even T U) :
    (even flatten v).length=2*k := by simp only [even,List.length_append,h]; omega

theorem odd_length {T U : Type} (flatten : U→List T) (k : Nat)
    (h : ∀ u, (flatten u).length=k) (v : Odd T U) :
    (odd flatten v).length=2*k+1 := by
  simp only [odd,List.length_append,List.length_singleton,h]
  omega

#print axioms even
#print axioms odd
#print axioms even_length
#print axioms odd_length
end R1Z.PV_CBL_GenericArrayFlatten
