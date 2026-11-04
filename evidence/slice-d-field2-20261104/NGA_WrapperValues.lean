import NGA_SumAlgebra
import NGA_Wrappers
set_option autoImplicit false
namespace NGA_WrapperValues
open Aeneas Aeneas.Std Result
open NGA_PreparePairs

theorem source {n : Usize} (left right : Array Q n) (arity : n.val≤4)
 (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 ∃ out, NGA_Wrappers.small left right=ok out ∧ Canonical out ∧
   AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=NGA_SumAlgebra.sumProducts (left.val.zip right.val) := by
 obtain ⟨length,canonical⟩ := NGA_Wrappers.domain left right hl hr
 exact NGA_SumAlgebra.source (left.val.zip right.val) (by rw [length];exact arity) canonical

theorem two (left right : Array Q 2#usize)
 (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 ∃ out, NGA_Wrappers.sum2 left right=ok out ∧ Canonical out ∧
   AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=NGA_SumAlgebra.sumProducts (left.val.zip right.val) :=
 source left right (by decide) hl hr

theorem three (left right : Array Q 3#usize)
 (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 ∃ out, NGA_Wrappers.sum3 left right=ok out ∧ Canonical out ∧
   AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=NGA_SumAlgebra.sumProducts (left.val.zip right.val) :=
 source left right (by decide) hl hr

theorem four (left right : Array Q 4#usize)
 (hl : ∀ x∈left.val, Canonical x) (hr : ∀ x∈right.val, Canonical x) :
 ∃ out, NGA_Wrappers.sum4 left right=ok out ∧ Canonical out ∧
   AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=NGA_SumAlgebra.sumProducts (left.val.zip right.val) :=
 source left right (by decide) hl hr

#print axioms source
#print axioms two
#print axioms three
#print axioms four
end NGA_WrapperValues
