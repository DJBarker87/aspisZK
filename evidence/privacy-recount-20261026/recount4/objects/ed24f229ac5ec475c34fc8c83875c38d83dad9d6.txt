import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op128Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op128
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op128Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op128_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ {Z : Type} (inst : zeroize.Zeroize Z) (x : Z),
    (PV_Join_Wire_Selection.selected base ops).op128 inst x =
      PV_CB_ShippedOp128.zeroize.Zeroizing.new inst x := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro Z inst x
  exact R1Z.PV_CB_Op128Source.op128_source ops inst x
#print op128_source
#print axioms op128_source
end R1Z.PV_Join_Wire_Op128
