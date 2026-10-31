import R1Z.PV_RunJoin_NativeFilledSize64
import R1Z.PV_RunJoin_LayoutConstants64
import R1Z.PV_RunJoin_QueryCommitmentWords64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeCommitmentLeaves64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (c : host_commitment.Commitment)
    (small : c.lanes.length≤29) (lanes : ∀ lane∈c.lanes.val,lane.val<29)
    (hash : aspis_core.digest.LegacyHashFn) (salts : host_commitment.PrivateSalts)
    (out : alloc.vec.Vec (Array U8 32#usize))
    (success : @host_commitment.commitment_leaves (types base) (opsNative base heap box ops runtime world)
      hash c.time (alloc.vec.Vec.deref c.lanes) (alloc.vec.Vec.deref c.words) (some salts)=ok (.Ok out)) :
    PV_RunJoin_QueryFillStep64.Domain c := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  unfold host_commitment.commitment_leaves at success
  rw [PV_RunJoin_LayoutConstants64.fibres] at success
  simp only [bind_tc_ok] at success
  obtain ⟨status,hstatus,rest⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
  cases status with
  | Err e => cases rest
  | Ok leaves =>
    have size : leaves.length=262144 := PV_RunJoin_ResultPost41.success _ _ (.Ok leaves)
      (PV_RunJoin_NativeFilledSize64.complete base heap box ops runtime world _ 262144#usize
        (Array.repeat 32#usize 0#u8)) hstatus
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
    obtain ⟨tag,htag,rest⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ rest
    obtain ⟨next,hnext,rest⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ rest
    exact PV_RunJoin_QueryCommitmentWords64.complete c small lanes hash tag salts leaves next size hnext

#print axioms complete
end R1Z.PV_RunJoin_NativeCommitmentLeaves64
