import R1Z.PV_RunJoin_ProducedRows72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ProducedClaims72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (p : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (point : Array Q 10#usize) :
    letI : ExternalTypes := types base
    ∃ out,@host_semantic.point_claims (types base)
      (opsNative base heap box ops runtime world) p.val.sem.columns point=ok (.Ok out) := by
  letI : ExternalTypes := types base
  exact PV_RunJoin_NativePointClaims72.complete base heap box ops runtime world p.val.sem.columns point
    (PV_RunJoin_ProducedRows72.native base heap box ops runtime world p)

#print axioms complete
end R1Z.PV_RunJoin_ProducedClaims72
