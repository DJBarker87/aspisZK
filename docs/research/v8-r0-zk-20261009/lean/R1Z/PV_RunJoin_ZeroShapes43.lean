import R1Z.PV_RunJoin_RecordPost43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ZeroShapes43
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem shape (ops : ExternalFuns) (i : Usize) (small : i.val<10) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops)
      (U8.wrapping_add 3#u8 (UScalar.cast .U8 i))=.ok (some (0#u8,0#usize)) := by
  have cases : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 ∨ i.val=8 ∨ i.val=9 := by omega
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · have hi : i=0#usize := UScalar.eq_of_val_eq h0
    subst i
    rfl
  · have hi : i=1#usize := UScalar.eq_of_val_eq h1
    subst i
    rfl
  · have hi : i=2#usize := UScalar.eq_of_val_eq h2
    subst i
    rfl
  · have hi : i=3#usize := UScalar.eq_of_val_eq h3
    subst i
    rfl
  · have hi : i=4#usize := UScalar.eq_of_val_eq h4
    subst i
    rfl
  · have hi : i=5#usize := UScalar.eq_of_val_eq h5
    subst i
    rfl
  · have hi : i=6#usize := UScalar.eq_of_val_eq h6
    subst i
    rfl
  · have hi : i=7#usize := UScalar.eq_of_val_eq h7
    subst i
    rfl
  · have hi : i=8#usize := UScalar.eq_of_val_eq h8
    subst i
    rfl
  · have hi : i=9#usize := UScalar.eq_of_val_eq h9
    subst i
    rfl
#print axioms shape
end R1Z.PV_RunJoin_ZeroShapes43
