import FSV8FiniteTapePrefix
import AspisFormal.K1.V7Tag73OperationalOracleExposure

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7FiniteTapeEmbedding
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSFreshTapeTrace FSV8PostOODGammaScript FSV8FreshTapeBudget
open FSV8FiniteTapePrefix
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev Point := FSV8PostOODGammaScript.Point

/-- The V7 inductive tape containing the first `steps` answers of the current
    Nat-indexed tape, in exactly the same left-to-right order. -/
def v7FreshTape (tape : Tape) : (steps : Nat) →
    FreshAnswerTape Digest256 steps
  | 0 => PUnit.unit
  | steps + 1 =>
      (tape 0, v7FreshTape (fun j => tape (j + 1)) steps)

theorem v7FreshTape_toList (tape : Tape) (steps : Nat) :
    freshAnswerTapeToList (v7FreshTape tape steps) =
      (List.range steps).map tape := by
  induction steps generalizing tape with
  | zero => rfl
  | succ steps ih =>
      simp only [v7FreshTape, freshAnswerTapeToList, List.range_succ_eq_map,
        List.map_cons, List.map_map]
      rw [ih]
      rfl

/-- The finite V7 tape representation is injective under its ordered list
    projection.  Thus the list embedding is an equivalence onto its image;
    no infinite tape object is introduced. -/
theorem freshAnswerTapeToList_injective {Output : Type} {steps : Nat}
    (left right : FreshAnswerTape Output steps)
    (equal : freshAnswerTapeToList left = freshAnswerTapeToList right) :
    left = right := by
  induction steps with
  | zero => cases left; cases right; rfl
  | succ steps ih =>
      cases left with
      | mk leftHead leftTail =>
        cases right with
        | mk rightHead rightTail =>
          simp only [freshAnswerTapeToList, List.cons.injEq] at equal
          rcases equal with ⟨headEqual, tailEqual⟩
          subst rightHead
          have tailEq : leftTail = rightTail := ih leftTail rightTail tailEqual
          subst rightTail
          rfl

theorem sourceThenGamma_v7_tape_embedding {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) :
    let final := run tape
      (sourceThenGammaScript firstWork secondWork body digest)
      (FSFirstFresh.empty : Oracle)
    let budget := sourceThenGammaBudget n m
    freshAnswers final.2.log =
      List.take final.2.next
        (freshAnswerTapeToList (v7FreshTape tape budget)) ∧
    final.2.next ≤ budget := by
  let final := run tape
    (sourceThenGammaScript firstWork secondWork body digest)
    (FSFirstFresh.empty : Oracle)
  let budget := sourceThenGammaBudget n m
  obtain ⟨exactPrefix, bounded⟩ :=
    sourceThenGamma_consumed_prefix firstWork secondWork body digest tape
  refine ⟨?_, bounded⟩
  rw [v7FreshTape_toList]
  rw [exactPrefix]
  rw [← List.map_take]
  simp [List.take_range, bounded]

/- Overflow is explicit: an execution that would consume beyond the finite V7
   tape is excluded by the deterministic budget theorem, rather than silently
   appealing to an infinite extension. -/
theorem sourceThenGamma_no_overflow {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) :
    ¬ sourceThenGammaBudget n m <
      (run tape (sourceThenGammaScript firstWork secondWork body digest)
        (FSFirstFresh.empty : Oracle)).2.next := by
  exact Nat.not_lt_of_ge
    (sourceThenGamma_fresh_budget firstWork secondWork body digest tape)

theorem sourceThenGamma_v7_finite_input {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) :
    ∃ finiteTape : FreshAnswerTape Digest256 (sourceThenGammaBudget n m),
      freshAnswerTapeToList finiteTape =
        (List.range (sourceThenGammaBudget n m)).map tape ∧
      freshAnswers
          (run tape (sourceThenGammaScript firstWork secondWork body digest)
            (FSFirstFresh.empty : Oracle)).2.log =
        List.take
          ((run tape (sourceThenGammaScript firstWork secondWork body digest)
            (FSFirstFresh.empty : Oracle)).2.next)
          (freshAnswerTapeToList finiteTape) := by
  refine ⟨v7FreshTape tape (sourceThenGammaBudget n m),
    v7FreshTape_toList tape _, ?_⟩
  exact (sourceThenGamma_v7_tape_embedding firstWork secondWork body digest tape).1

#print axioms v7FreshTape_toList
#print axioms freshAnswerTapeToList_injective
#print axioms sourceThenGamma_v7_tape_embedding
#print axioms sourceThenGamma_no_overflow
#print axioms sourceThenGamma_v7_finite_input
end AspisV8Completion.FSV8V7FiniteTapeEmbedding
