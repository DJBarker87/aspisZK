import SharedTensorContraction
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
open scoped BigOperators
namespace AspisR1S9SharedContiguousContractionV1
/-- Actual contiguous source offset: the four slots occupy successive
sixteen-field blocks. This preserves the implemented order. -/
def sourceIndex (slot : Fin 4) (j : Fin 16) : Fin 64 := finProdFinEquiv (slot,j)
theorem sourceIndex_val (slot : Fin 4) (j : Fin 16) :
    (sourceIndex slot j).val=j.val+16*slot.val := rfl

def tensorWeight {E : Type*} [Mul E] (low : Fin 16 → E) (high : Fin 4 → E)
    (i : Fin 64) : E :=
  let ij : Fin 4 × Fin 16 := finProdFinEquiv.symm i
  low ij.2*high ij.1

/-- Existing proved 4-by-16 contraction in the exact contiguous 64-field
source order. This is a pure algebraic bridge; source read meanings must be
supplied by actual accepted execution proofs. -/
theorem contiguous_contract {E : Type*} [CommSemiring E]
    (f : Fin 64 → E) (low : Fin 16 → E) (high : Fin 4 → E) :
    (∑ i : Fin 64, f i*tensorWeight low high i)=
      ∑ slot : Fin 4, (∑ j : Fin 16, f (sourceIndex slot j)*low j)*high slot := by
  rw [←(finProdFinEquiv (m:=4) (n:=16)).sum_comp,Fintype.sum_prod_type]
  simpa only [tensorWeight,sourceIndex,Equiv.symm_apply_apply] using
    (AspisR1.SharedTensorContraction.contract
      (fun slot j => f (sourceIndex slot j)) low high)
#print axioms sourceIndex_val
#print axioms contiguous_contract
end AspisR1S9SharedContiguousContractionV1
