import R1Z.PV_CB3_StagedPacking
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedCast
open Aeneas Aeneas.Std
#print UScalar.cast
#print UScalar.mk
#print UScalar.bv
/-- The narrowed source scalar carries exactly the low machine bits. -/
theorem narrow (r : BitVec 64) :
    UScalar.cast .U32 (⟨r⟩ : U64) = (⟨r.setWidth 32⟩ : U32) := by
  apply UScalar.eq_of_val_eq
  simp [UScalar.cast]
#print axioms narrow
end R1Z.PV_CB3_StagedCast
