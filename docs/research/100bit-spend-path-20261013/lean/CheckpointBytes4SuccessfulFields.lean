import CheckpointBytes4SavedFields
import CheckpointBytes4Next
import CheckpointBytes4Comparison

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4SuccessfulFields
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Ops CheckpointBytes4SavedFields
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep OraclePortCompactDraft
open MultiproofConeCanonical OraclePortCheckpointAbiC5

/-- Every successful concrete callback execution returns all saved fields.
Encoding is input/state provenance, not an output or observation equality.
Allocation success is derived from execution and is not an added premise. -/
theorem successful_saved_fields (reserved : Bool) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (ck proof public1 : Slice U8) (hash : Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State) (stored pub : Bytes) (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K E)
    (encoding : bytesOf ck.val = encode H stored pub pm am) (next : am.next = 10)
    (success : verifier.resumeWithOps (ops reserved) D ck proof public1 .S2 hash = ok (.Ok (p,a))) :
    BodyMatches p a pm am ∧ a.next.val = am.next ∧ reserved = true := by
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D ck proof public1 .S2 hash p a success
  refine ⟨body_matches reserved ck p a f H stored pub pm am encoding,?_,?_⟩
  · rw [next]
    exact CheckpointBytes4Next.next_value reserved ck p a f H stored pub pm am encoding
  · exact (CheckpointBytes3Allocation.filled_success_content reserved f.finalLength f.zero
      f.allocated f.allocation).1

#print axioms successful_saved_fields
end AspisR1.CheckpointBytes4SuccessfulFields
end
