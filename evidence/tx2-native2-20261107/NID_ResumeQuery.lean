import NID_ResumeCallerDomain
set_option autoImplicit false
noncomputable section
namespace NID_ResumeQuery
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem weights (a : verifier.Accumulator)
 (canonical : ∀ x ∈ a.weights.val, NID_ResumeCanonical.KCanonical x) :
 NFS_NEV_WeightDomains.Canonical (NEV_AccumulateCarriers.fromAccumulator a).weights := by
 intro q hq
 change q ∈ a.weights.val.map NEV_AccumulateCarriers.fromQ at hq
 obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
 rw [NEV_AccumulateCarriers.q_reverse]
 exact NID_ResumeCallerDomain.power x (canonical x hx)

/-- Discharge the concrete NFW query entry domain from the same reader return.
The start10 fact is the parent driver's guard; resume itself permits next≤22. -/
theorem domain (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) (p : verifier.Prepared) (a : verifier.Accumulator)
 (size : ck.val.length=1768)
 (success : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D ck proof pub .S2 hash=ok (.Ok (p,a)))
 (start : a.next.val=10) :
 NFS_QueryInvariant.Domain p 10 22 a (NFW_QueryResume.pending a) ∧
 NFN_LPi_FieldValues.canonE (FIo_Install.toE p.gamma) := by
 have d := NID_ResumeFields.returned reserved D ck proof pub hash p a size success
 exact ⟨NFW_QueryResume.domain p a d.width (weights a d.weights)
  (NID_ResumeCallerDomain.wide a.rhs d.rhs)
  (NID_ResumeCallerDomain.power a.power d.power)
  (NID_ResumeCallerDomain.power p.rho d.rho) start,
  NID_ResumeCallerDomain.gamma p.gamma d.gamma⟩
#print axioms weights
#print axioms domain
end NID_ResumeQuery
