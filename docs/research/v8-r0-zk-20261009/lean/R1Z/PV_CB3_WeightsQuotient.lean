import Aeneas
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsQuotient
open Aeneas Aeneas.Std Result

theorem remainder (x y : Usize) (h : y.val ≠ 0) :
    ∃ r, UScalar.rem x y = ok r ∧ r.val = x.val % y.val := by
  unfold UScalar.rem
  rw [if_pos (by simpa using h)]
  refine ⟨_,rfl,?_⟩
  change (x.bv.umod y.bv).toNat = _
  exact BitVec.toNat_umod

theorem quotient (x y : Usize) (h : y.val ≠ 0) :
    ∃ q, UScalar.div x y = ok q ∧ q.val = x.val / y.val := by
  have hb : y.bv ≠ 0#(UScalarTy.numBits .Usize) := by
    intro hz
    apply h
    have hv := congrArg BitVec.toNat hz
    exact hv
  unfold UScalar.div
  rw [if_pos (by simpa using hb)]
  refine ⟨_,rfl,?_⟩
  change (x.bv.udiv y.bv).toNat = _
  exact BitVec.toNat_udiv
#print axioms remainder
#print axioms quotient
end R1Z.PV_CB3_WeightsQuotient
