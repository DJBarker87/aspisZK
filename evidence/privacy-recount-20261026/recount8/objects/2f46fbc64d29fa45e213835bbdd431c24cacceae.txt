import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op130Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op130
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op130Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op130_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ {Z : Type} (inst : zeroize.Zeroize Z) (x : Z),
    (PV_Join_Wire_Selection.selected base ops).op130 inst x =
      PV_CB_ShippedOp130.zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize inst x := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro Z inst x
  exact R1Z.PV_CB_Op130Source.op130_source ops inst x
#print op130_source
#print axioms op130_source
end R1Z.PV_Join_Wire_Op130
