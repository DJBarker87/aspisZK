import DecodedFirstReadUnionBound

/-! Count actual decoder-start opportunities on the retained chronological
trace and convert a uniform trace count to the causal union-bound interface. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DecodedFirstReadUnionBound
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
attribute [local instance] Classical.propDecidable
variable {X M C I A Y O : Type} [DecidableEq I]

/-- Number of fresh trace cells for which the causal input/table decoder
returns a chain start. This is a direct event-opportunity count. -/
def decoderFirstReads (dec : Dec X M C I A Y) : Table I A → List (I × A) → Nat
  | _, [] => 0
  | t, (i,a)::rest =>
    (if t i = none ∧ dec i t ≠ none then 1 else 0) +
      decoderFirstReads dec (put t i a) rest

theorem decoderFirstReads_le_firstReads (dec : Dec X M C I A Y)
    (t : Table I A) (tr : List (I × A)) :
    decoderFirstReads dec t tr ≤ firstReads t tr := by
  induction tr generalizing t with
  | nil => rfl
  | cons cell rest ih =>
    rcases cell with ⟨i,a⟩
    have hr := ih (put t i a)
    cases ht : t i with
    | none =>
      by_cases hd : dec i t = none
      · simp only [decoderFirstReads, firstReads, ht, hd, ne_eq, not_true_eq_false,
          and_false, if_false] at *
        omega
      · simp only [decoderFirstReads, firstReads, ht, hd, ne_eq, not_false_eq_true,
          and_self, if_true] at *
        omega
    | some b =>
      simp only [decoderFirstReads, firstReads, ht, reduceCtorEq, false_and,
        if_false, zero_add] at *
      exact hr

/-- Any proved actual trace bound supplies the recursive memoized experiment
budget, without evaluating a huge concrete transcript. -/
theorem decoderReadsBound_of_traces [Nonempty A]
    (dec : Dec X M C I A Y) (p : Program I A O) :
    ∀ (t : Table I A) (N : Nat),
      (∀ H : I → A, decoderFirstReads dec t (eval (complete t H) p).1 ≤ N) →
      DecoderReadsBound dec p t N := by
  induction p with
  | done o => intros; trivial
  | ask i next ih =>
    intro t N hN
    cases ht : t i with
    | some a =>
      simp only [DecoderReadsBound, ht]
      apply ih a t N
      intro H
      have hb := hN H
      simpa only [eval, complete_cached t H i a ht, decoderFirstReads, ht,
        reduceCtorEq, false_and, if_false, zero_add, put_self t i a ht] using hb
    | none =>
      by_cases hd : dec i t = none
      · simp only [DecoderReadsBound, ht, hd, if_true]
        intro a
        apply ih a (put t i a) N
        intro H
        have hb := hN (Function.update H i a)
        simp only [eval, complete_missing t (Function.update H i a) i ht,
          Function.update_self, decoderFirstReads, ht, hd, ne_eq,
          not_true_eq_false, and_false, if_false, zero_add] at hb
        rw [complete_resample t H i a ht] at hb
        exact hb
      · simp only [DecoderReadsBound, ht, if_neg hd]
        have hone : ∀ H : I → A, 1 + decoderFirstReads dec (put t i (H i))
            (eval (complete t H) (next (H i))).1 ≤ N := by
          intro H
          have hb := hN H
          simpa only [eval, complete_missing t H i ht, decoderFirstReads, ht,
            hd, ne_eq, not_false_eq_true, and_self, if_true] using hb
        refine ⟨?_, ?_⟩
        · obtain ⟨a⟩ := (inferInstance : Nonempty A)
          have hb := hone (fun _ => a)
          omega
        · intro a
          apply ih a (put t i a) (N-1)
          intro H
          have hb := hone (Function.update H i a)
          simp only [Function.update_self] at hb
          rw [complete_resample t H i a ht] at hb
          omega

#print axioms decoderFirstReads_le_firstReads
#print axioms decoderReadsBound_of_traces
end AspisR1.DecodedFirstReadUnionBound
end
