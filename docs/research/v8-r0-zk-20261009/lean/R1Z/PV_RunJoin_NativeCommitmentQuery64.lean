import R1Z.PV_RunJoin_NativeCommitmentDomain64
import R1Z.PV_RunJoin_NativeCommitmentSalt64
import R1Z.PV_RunJoin_CommitmentLanes64
import R1Z.PV_RunJoin_CommitmentTrace64
import R1Z.PV_RunJoin_NativeOptionRef64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeCommitmentQuery64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (hash : aspis_core.digest.LegacyHashFn) (domain : host_commitment.EncodingDomain)
    (time : host_commitment.CommitmentTime)
    (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (variant : transport.Variant) (salts : host_commitment.PrivateSalts)
    (c : host_commitment.Commitment)
    (success : @host_commitment.Commitment.build (types base) (opsNative base heap box ops runtime world)
      hash domain time messages variant (some salts)=ok (.Ok c)) :
    PV_RunJoin_QueryFillStep64.Domain c ∧
      ∃ s, c.private_salts=some s ∧ 262144≤s.length := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨htime,hstored,hlanes,saltRef,href,leaves,hleaves⟩ :=
    PV_RunJoin_CommitmentTrace64.complete hash domain time messages variant (some salts) c success
  change (opsNative base heap box ops runtime world).op6 (some salts)=ok saltRef at href
  rw [PV_RunJoin_NativeOptionRef64.complete] at href
  have same : some salts=saltRef := Result.ok.inj href
  subst saltRef
  have reached : host_commitment.commitment_leaves hash c.time (alloc.vec.Vec.deref c.lanes)
      (alloc.vec.Vec.deref c.words) (some salts)=ok (.Ok leaves) := by
    rw [htime]
    exact hleaves
  have words := (PV_RunJoin_NativeCommitmentDomain64.complete base heap box ops runtime world
    hash domain time messages variant salts c success).1
  exact ⟨words,salts,hstored,PV_RunJoin_NativeCommitmentSalt64.complete base heap box ops runtime world
    c hash salts leaves reached⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeCommitmentQuery64
