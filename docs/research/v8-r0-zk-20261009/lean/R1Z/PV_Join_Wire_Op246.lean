import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB3_Op246Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op246
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB3_Op246Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op246_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ {H : Type}
    (inst : aspis_core.digest.Digest32 H) (hash : H)
    (left right : Array U8 32#usize),
    (PV_Join_Wire_Selection.selected base ops).op246 inst hash left right =
      PV_CB3_ShippedOp246.multiproof.binary_parent inst hash left right := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro H inst hash left right
  change PV_CB3_ShippedOp246.multiproof.binary_parent inst hash left right = _
  exact (PV_CB3_Op246Source.op246_source ops inst hash left right).symm.trans
    (PV_CB3_Op246Source.op246_source ops inst hash left right)
#print op246_source
#print axioms op246_source
end R1Z.PV_Join_Wire_Op246
