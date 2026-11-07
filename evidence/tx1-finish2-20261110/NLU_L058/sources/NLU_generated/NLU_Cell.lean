import NLU_State
set_option autoImplicit false
namespace AspisR1.NLU
open Aeneas Aeneas.Std
/-- Standard bounded value projection, without importing historical driver
support. Bounds are on the value's own fixed array type. -/
def cell {A : Type} {N : Usize} (a : Array A N) (i : Nat) (h : i<N.val) : A :=
 a.val[i]'(by have len:=a.property;omega)
theorem cells_ext {A : Type} {N : Usize} (a b : Array A N)
 (same : ∀ i (h : i<N.val),cell a i h=cell b i h) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem
 · have ha:=a.property;have hb:=b.property;omega
 · intro i ha hb
   exact same i (by have len:=a.property;omega)
#print axioms cells_ext
end AspisR1.NLU
