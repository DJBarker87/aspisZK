import R1Z.PV_RunJoin_NativeMultilinear72
import R1Z.PV_RunJoin_PointsTotal72
import R1Z.PV_RunJoin_PointClaimsSuff69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePointClaims72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

def Rows (columns : Array (alloc.vec.Vec Q) 29#usize) : Prop :=
  ∀ (lane : Usize) (v : alloc.vec.Vec Q), lane.val<29 →
    Array.index_usize columns lane=ok v → v.length=1024

theorem points {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (point : Array Q 10#usize) :
    ∃ out,@r1_wire.statement_points (types base)
      (opsNative base heap box ops runtime world) point=ok out := by
  rw [PV_RunJoin_NativeClaimsApi69.points]
  exact PV_RunJoin_PointsTotal72.complete point

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (columns : Array (alloc.vec.Vec Q) 29#usize) (point : Array Q 10#usize)
    (rows : Rows columns) :
    letI : ExternalTypes := types base
    ∃ out,@host_semantic.point_claims (types base)
      (opsNative base heap box ops runtime world) columns point=ok (.Ok out) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨ps,hps⟩ := points base heap box ops runtime world point
  apply PV_RunJoin_PointClaimsSuff69.complete
    (PV_RunJoin_NativeClaimsApi69.some_ok base heap box ops runtime world)
    ⟨_,PV_RunJoin_NativeQuarticTotal69.zero_source base heap box ops runtime world⟩
    columns point ps hps
  intro p lane v hl hv
  exact PV_RunJoin_NativeMultilinear72.complete base heap box ops runtime world
    (alloc.vec.Vec.deref v) p (rows lane v hl hv)

#print axioms Rows
#print axioms points
#print axioms complete
end R1Z.PV_RunJoin_NativePointClaims72
