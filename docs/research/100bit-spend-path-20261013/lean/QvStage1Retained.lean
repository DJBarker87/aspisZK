import WireTx1DigestCalls

/-! Exact call-equation witnesses for the retained fifteen-row begin fragment.
These are dictionary equations, not a proof of runtime effect-log completeness. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.WireTx1
open r1_wire TranscriptStep

abbrev DigestWitness (H : Type) := H × Slice (Slice U8) × Bytes32

def WitnessValid {H : Type} (D : aspis_core.Digest32 H) (q : DigestWitness H) : Prop :=
  D.digest q.1 q.2.1 = ok q.2.2

theorem run_call_witnesses {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) {rows self after qs}
    (run : TypedSemanticRun D pre rows self after qs) :
    ∃ calls : List (DigestWitness H),
      calls.length = 3 * rows.length ∧ ∀ q ∈ calls, WitnessValid D q := by
  induction run with
  | nil => exact ⟨[], by simp, by simp⟩
  | @cons row rows self mid after q qs record block tag absorbed state
      accessor call absorbCall blockCall advanceCall typed tail ih =>
    obtain ⟨calls, hlen, hvalid⟩ := ih
    refine ⟨(self.hash, TranscriptStep.absorbParts self.state tag record.framed, absorbed) ::
      (self.hash, TranscriptStep.readParts absorbed 1#u8, block) ::
      (self.hash, TranscriptStep.readParts absorbed 2#u8, state) :: calls, ?_, ?_⟩
    · simp only [List.length_cons, hlen]
      omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | hx
      · exact absorbCall
      · exact blockCall
      · exact advanceCall
      · exact hvalid x hx

/-- Actual successful retained begin produces 45 ordered digest-equation
witnesses. The initializer and rows 15..26 are outside this fragment. -/
theorem begin_45_call_witnesses {H : Type} (D : aspis_core.Digest32 H)
    (bytes : Slice U8) (pre : r1_wire.Prefix) (hp : Parsed bytes pre)
    (self after : r1_wire.SemanticTranscript H) (out : r1_wire.Challenges)
    (h : r1_wire.begin D pre self = ok (.Ok out, after)) :
    ∃ calls : List (DigestWitness H),
      calls.length = 45 ∧ ∀ q ∈ calls, WitnessValid D q := by
  obtain ⟨calls, hlen, hv⟩ := run_call_witnesses D pre (begin_typed D bytes pre hp self after out h)
  exact ⟨calls, hlen, hv⟩

#print axioms run_call_witnesses
#print axioms begin_45_call_witnesses
end AspisR1PublicPreparation.WireTx1
