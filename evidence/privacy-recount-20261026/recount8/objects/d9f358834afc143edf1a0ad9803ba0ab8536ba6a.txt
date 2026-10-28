import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op131Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op131
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op131Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op131_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ {T Z : Type}
    (view : core.convert.AsRef Z T) (inst : zeroize.Zeroize Z) (x : Z),
    (PV_Join_Wire_Selection.selected base ops).op131 view inst x =
      PV_CB_ShippedOp131.zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref view inst x := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro T Z view inst x
  exact R1Z.PV_CB_Op131Source.op131_source ops view inst x
#print op131_source
#print axioms op131_source
end R1Z.PV_Join_Wire_Op131
