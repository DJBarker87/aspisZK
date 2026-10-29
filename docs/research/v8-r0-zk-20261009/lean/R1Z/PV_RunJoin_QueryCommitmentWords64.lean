import R1Z.PV_RunJoin_QueryStoredWords64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryCommitmentWords64
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem complete (c : host_commitment.Commitment)
    (small : c.lanes.length≤29) (lanes : ∀ lane∈c.lanes.val,lane.val<29)
    (hash : aspis_core.digest.LegacyHashFn) (tag : U8) (salts : host_commitment.PrivateSalts)
    (leaves out : alloc.vec.Vec (Array U8 32#usize)) (length : leaves.length=262144)
    (success : host_commitment.salted_commitment_leaves hash tag (alloc.vec.Vec.deref c.lanes)
      (alloc.vec.Vec.deref c.words) salts leaves=ok out) :
    PV_RunJoin_QueryFillStep64.Domain c := by
  obtain ⟨payload,hpayload⟩ := PV_RunJoin_QueryLeafVisit64.visited hash tag
    (alloc.vec.Vec.deref c.lanes) (alloc.vec.Vec.deref c.words) salts (alloc.vec.Vec.len leaves)
    (by change leaves.length≤262144;omega) leaves out 0#usize 262143#usize
    (by decide) (by change 262143<leaves.length;omega) success
  exact PV_RunJoin_QueryStoredWords64.complete c small lanes payload hpayload

#print axioms complete
end R1Z.PV_RunJoin_QueryCommitmentWords64
