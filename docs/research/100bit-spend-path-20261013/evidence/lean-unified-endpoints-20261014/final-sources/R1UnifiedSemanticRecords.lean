import R1UnifiedPhases
import R1RawRecordSplit

/-! The unified record list equals the record constructor applied to the
previous-state function. This is list/index bookkeeping only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticRecords

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}
variable (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
  (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)

theorem records_eq (n : Nat) :
    RawRoundCompletion.recs
      (UnifiedRecords.previous p hD H pub c1 payload)
      (UnifiedRecords.absorbed p hD H pub c1 payload) payload
      (fun j => UnifiedRecords.previous p hD H pub c1 payload (j + 1)) n =
    UnifiedRecords.records p hD H pub c1 payload n := by
  unfold UnifiedRecords.records
  apply RawRecordSplit.recs_congr
  intro j hj
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact UnifiedPhases.previous_state p hD H pub c1 payload (j + 1) (by omega)

#print axioms records_eq

end AspisR1.UnifiedSemanticRecords
end
