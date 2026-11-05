import NID_ResumeFields
import NID_NCI_QueryInvariant
set_option autoImplicit false
noncomputable section
namespace NID_ResumeQueries
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Query bounds and distinctness come from the validation actually executed
on the SAME returned Prepared, not an independent query array or Merkle root. -/
theorem returned (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) (p : verifier.Prepared) (a : verifier.Accumulator)
 (success : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D ck proof pub .S2 hash=ok (.Ok (p,a))) :
 (∀ q ∈ p.queries.val, q.val<262144) ∧ p.queries.val.Nodup := by
 obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D ck proof pub .S2 hash p a success
 have validated : CheckpointBytes4Ops.queryLoop [] p.queries.val=core.result.Result.Ok () := Result.ok.inj f.validate
 exact ⟨NCI_QueryInvariant.accepted_bounds [] _ validated,
  NCI_QueryInvariant.accepted_unique [] _ validated⟩
#print axioms returned
end NID_ResumeQueries
