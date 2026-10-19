import R1SelectedSemanticPrefixFacts
import R1RawRoundCompletion
import R1RawRoundAppend
import R1SelectedChallengeMap

/-! Challenge-pair views of completed selected records. These list identities
connect the semantic prefix parser and the abstract completed-round sampler;
they do not assert transcript-source or probability correspondence. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedCompletedSemantic

open FS FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep
open AspisR1.InitialWalk
open AspisR1.SelectedTranscriptParams
open R0P.Mask R0P.SemSource

abbrev Message := SelectedTranscriptParams.Message

/-- Keep each completed message paired with its challenge, discarding only
its next-state component. -/
def pairs (T : Table (Addr SelectedTranscriptParams.L) State)
    (acc : Addr SelectedTranscriptParams.L → State) (offset : Nat)
    (rs : List (Rec Message)) : List (Message × AspisWideTower.WideExact) :=
  (completeRounds SelectedTranscriptParams.params T acc offset rs).map
    (fun q => (q.1, q.2.1))

theorem pairs_append (T : Table (Addr SelectedTranscriptParams.L) State)
    (acc : Addr SelectedTranscriptParams.L → State) (offset : Nat)
    (left right : List (Rec Message)) :
    pairs T acc offset (left ++ right) =
      pairs T acc offset left ++ pairs T acc (offset + left.length) right := by
  unfold pairs
  rw [RawRoundAppend.completeRounds_append_list]
  simp only [List.map_append]

theorem semChalsZ_read
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (offset : Nat) (T : Table (Addr SelectedTranscriptParams.L) State)
    (acc : Addr SelectedTranscriptParams.L → State) (rs : List (Rec Message))
    (out : List (SemMsgZ AspisWideTower.WideExact × AspisWideTower.WideExact))
    (hread : SelectedSemanticPrefix.read recoverC2 offset (pairs T acc offset rs) = some out) :
    semChalsZ (SelectedSemanticPrefixFacts.lift out) =
      some ((pairs T acc offset rs).map Prod.snd) :=
  SelectedSemanticPrefixFacts.semChalsZ_read recoverC2 offset
    (pairs T acc offset rs) out hread

theorem semantic_recs_challenges
    (H : Addr SelectedTranscriptParams.L → State)
    (ss absorbed : Nat → State) (msg : Nat → Message) (next : Nat → State)
    (n : Nat) (hn : n ≤ 25) :
    (pairs emptyTable H 0 (RawRoundCompletion.recs ss absorbed msg next n)).map Prod.snd =
      (List.range n).map
        (fun j => R0P.SemSource.semChal
          (H (squeezeA SelectedTranscriptParams.params (absorbed j)))) := by
  simp only [pairs, RawRoundCompletion.complete_recs, List.map_map,
    Function.comp_apply, Nat.zero_add, emptyTable, Option.getD_none]
  apply List.map_congr_left
  intro j hj
  have hjn : j < n := List.mem_range.mp hj
  change SelectedTranscriptParams.params.σ j (H (squeezeA SelectedTranscriptParams.params (absorbed j))) = _
  exact SelectedChallengeMap.semantic_row j (by omega) _

#print axioms pairs_append
#print axioms semChalsZ_read
#print axioms semantic_recs_challenges

end AspisR1.SelectedCompletedSemantic
end
