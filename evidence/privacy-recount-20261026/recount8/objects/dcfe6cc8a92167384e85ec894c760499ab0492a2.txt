import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op127Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op127
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op127Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op127_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ {Z : Type} (inst : zeroize.Zeroize Z) (x : Z),
    (PV_Join_Wire_Selection.selected base ops).op127 inst x =
      PV_CB_ShippedOp127.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst x := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro Z inst x
  exact R1Z.PV_CB_Op127Source.op127_source ops inst x
#print op127_source
#print axioms op127_source
end R1Z.PV_Join_Wire_Op127
