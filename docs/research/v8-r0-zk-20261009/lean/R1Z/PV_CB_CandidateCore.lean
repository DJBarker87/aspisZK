import R1Z.PV_CB_CandidateDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CandidateDictionary
open Aeneas Aeneas.Std Result ProverRwFull
theorem op3 (base : ExternalTypes) (ops : @ExternalFuns (native base)) {T : Type}
    (inst : core.default.Default T) (x : T) :
    (selected base ops).op3 inst x = PV_CB_ShippedTake.core.mem.take inst x := by
  letI : ExternalTypes := native base
  change (PV_CB_Take.selected ops).op3 inst x = _
  exact R1Z.PV_CB_TakeSource.op3_source ops inst x
#print axioms op3
theorem op77 (base : ExternalTypes) (ops : @ExternalFuns (native base)) {E : Type} (inst : core.clone.Clone E)
    (p : aspis_core.r0.domain.Point E) :
    (selected base ops).op77 inst p =
      PV_CB_ShippedOp77.aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone inst p := by
  letI : ExternalTypes := native base
  change (PV_CB_PointClone.selected ops).op77 inst p = _
  exact R1Z.PV_CB_Op77Source.op77_source ops inst p
#print axioms op77
theorem op82 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op82 = .ok PV_CB_ShippedOp82.aspis_core.r0.merkle.C1_TAG := by
  letI : ExternalTypes := native base
  change (PV_CB_Merkle.selected ops).op82 = _
  exact R1Z.PV_CB_Op82Source.op82_source ops
#print axioms op82
theorem op83 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op83 = .ok PV_CB_ShippedOp83.aspis_core.r0.merkle.C2_TAG := by
  letI : ExternalTypes := native base
  change (PV_CB_Merkle.selected ops).op83 = _
  exact R1Z.PV_CB_Op83Source.op83_source ops
#print axioms op83
theorem op84 (base : ExternalTypes) (ops : @ExternalFuns (native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (tag : U8) (values : Slice U8) :
    (selected base ops).op84 hash tag values =
      PV_CB_ShippedOp84Fresh.aspis_core.r0.merkle.leaf hash tag values := by
  letI : ExternalTypes := native base
  change (PV_CB_Op84Exact.selected ops).op84 hash tag values = _
  exact R1Z.PV_CB_Op84Exact.op84_source ops tag values
#print axioms op84
theorem op86 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op86 = .ok PV_CB_ShippedOp86.aspis_core.r0.opening.LANES := by
  letI : ExternalTypes := native base
  change (PV_CB_Merkle.selected ops).op86 = _
  exact R1Z.PV_CB_Op86Source.op86_source ops
#print axioms op86
end R1Z.PV_CB_CandidateDictionary
