import XRp_PowersQAdd
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_PowersNonvacuity
open XRp_PowersQAdd XRo_Join_Carriers

def zero : EQ := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem canonical : CanonicalQ zero := by
  change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647)
  decide

theorem source_zero : XRn_Join_Field.field.QM31.add zero zero = ok zero := by
  simp only [XRn_Join_Field.field.QM31.add,XRn_Join_Field.field.CM31.add,
    XRn_Join_Field.field.M31.add,XRn_Join_Field.field.P,zero]
  rfl

theorem both_succeed : XRn_Join_Field.field.QM31.add zero zero = ok zero ∧
    AspisR1CurrentWideMul.field.QM31.add (toQ zero) (toQ zero) = ok (toQ zero) := by
  refine ⟨source_zero,?_⟩
  have h := add zero zero canonical canonical
  rw [source_zero] at h
  exact h.symm

#print axioms canonical
#print axioms source_zero
#print axioms both_succeed
end XRp_PowersNonvacuity
