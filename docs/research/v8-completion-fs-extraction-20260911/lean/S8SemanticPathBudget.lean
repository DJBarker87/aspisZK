import S8BufferedPotential
import FSLiveSemanticPrefix

/-!
# S8 source-semantic path budget

Compositional call bounds for the actual semantic script.  These lemmas use
the path-sensitive eight-call candidate theorem, so the static 66-call Script
allowance is not charged.  Every bound is over complete oracle-log length and
therefore counts cache hits as well as fresh calls.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace AspisV8Completion.S8SemanticPathBudget

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31 FSLiveSemanticPrefix
open S8BufferedPotential
open SemanticWireExecution SameBodyAuthenticatedIncrement

abbrev Bytes := List UInt8
abbrev HB := FSBoundedTranscript.Block

def LogBound {A : Type} {n : Nat} (tape : Tape)
    (script : Script Bytes HB A n) (cost : Nat) : Prop :=
  ∀ oracle, (run tape script oracle).2.log.length ≤ oracle.log.length + cost

theorem logBound_done (tape : Tape) {A : Type} {n : Nat} (value : A) :
    LogBound tape (.done (n := n) value) 0 := by
  intro oracle
  simp only [run, Nat.add_zero]
  exact Nat.le_refl _

theorem logBound_done_cost (tape : Tape) {A : Type} {n : Nat} (value : A)
    (cost : Nat) : LogBound tape (.done (n := n) value) cost := by
  intro oracle
  simp only [run]
  omega

theorem logBound_pad (tape : Tape) {A : Type} {n : Nat}
    (script : Script Bytes HB A n) (extra cost : Nat)
    (bound : LogBound tape script cost) :
    LogBound tape (pad script extra) cost := by
  intro oracle
  rw [run_pad]
  exact bound oracle

theorem logBound_map (tape : Tape) {A B : Type} {n cost : Nat}
    (f : A → B) (script : Script Bytes HB A n)
    (bound : LogBound tape script cost) :
    LogBound tape (FSTranscriptScript.map f script) cost := by
  intro oracle
  rw [run_map]
  exact bound oracle

theorem logBound_bind (tape : Tape) {A B : Type} {n m firstCost restCost : Nat}
    (script : Script Bytes HB A n) (next : A → Script Bytes HB B m)
    (firstBound : LogBound tape script firstCost)
    (restBound : ∀ value, LogBound tape (next value) restCost) :
    LogBound tape (bind script next) (firstCost + restCost) := by
  intro oracle
  rw [run_bind]
  cases result : (run tape script oracle).1 with
  | none =>
      simp only [result]
      have first := firstBound oracle
      omega
  | some value =>
      simp only [result]
      have first := firstBound oracle
      have rest := restBound value (run tape script oracle).2
      omega

theorem absorbScript_logBound (tape : Tape) (digest : HB)
    (label : UInt8) (data : Bytes) :
    LogBound tape (absorbScript digest label data) 1 := by
  intro oracle
  simp only [absorbScript, run, S8BufferedPotential.query_log_length]
  exact Nat.le_refl _

theorem candidateScript_logBound (tape : Tape) (digest : HB) :
    LogBound tape (candidateScript digest) 8 := by
  intro oracle
  let start : Transcript := ⟨digest, oracle⟩
  simpa only [start] using source_candidateScript_log_length_le_eight tape start

theorem nonzeroScript_logBound (tape : Tape) (n : Nat) (digest : HB) :
    LogBound tape (nonzeroScript n digest) (8 * n) := by
  intro oracle
  let start : Transcript := ⟨digest, oracle⟩
  simpa only [start] using source_nonzeroScript_log_length_le tape n start

theorem optionalProfileScript_logBound (tape : Tape) (positive : Bool)
    (digest : HB) :
    LogBound tape (optionalProfileScript positive digest) 1 := by
  unfold optionalProfileScript
  split
  · exact absorbScript_logBound tape digest 1 selectedPositiveDescriptor
  · apply logBound_pad
    exact logBound_done_cost tape digest 1

theorem indexedCandidates_logBound (tape : Tape) : ∀ count index digest,
    LogBound tape (indexedCandidates count index digest) (8 * count) := by
  intro count
  induction count with
  | zero =>
      intro index digest
      simpa only [indexedCandidates, Nat.mul_zero] using
        logBound_done tape
          ((Except.ok [] : Except (Nat × FSNonzeroQM31.Error)
            (List FSLiveSemanticPrefix.K)), digest)
  | succ count ih =>
      intro index digest
      simp only [indexedCandidates]
      rw [show 8 * (count + 1) = 8 + 8 * count by omega]
      apply logBound_bind tape _ _ (candidateScript_logBound tape digest)
      intro draw
      cases draw.1 with
      | error error =>
          exact logBound_done_cost tape (Except.error (index, error), draw.2)
            (8 * count)
      | ok value =>
          apply logBound_map
          exact ih (index + 1) draw.2

theorem semanticRounds_logBound (tape : Tape) (body : Bytes)
    (values : List FSLiveSemanticPrefix.K) : ∀ remaining round claim digest,
    LogBound tape (semanticRounds body values remaining round claim digest)
      (9 * remaining) := by
  intro remaining
  induction remaining with
  | zero =>
      intro round claim digest
      simpa only [semanticRounds, Nat.mul_zero] using
        logBound_done tape (Except.ok (RoundState.mk [] claim digest))
  | succ remaining ih =>
      intro round claim digest
      simp only [semanticRounds]
      rw [show 9 * (remaining + 1) = 1 + (8 + 9 * remaining) by omega]
      apply logBound_bind tape _ _
        (absorbScript_logBound tape digest 48 (semanticRoundBytes body round))
      intro afterMessage
      apply logBound_bind tape _ _ (candidateScript_logBound tape afterMessage)
      intro draw
      cases draw.1 with
      | error error =>
          exact logBound_done_cost tape (Except.error (round, error))
            (9 * remaining)
      | ok alpha =>
          apply logBound_map
          exact ih (round + 1)
            (evaluate exactArithmetic
              (polynomial exactArithmetic claim
                (sent (wordOfValues values)
                  ⟨round % 10, Nat.mod_lt _ (by decide)⟩)) alpha)
            draw.2

/-- The selected positive-transfer semantic transcript performs at most 234
actual shared-oracle calls on every parser, retry, cache and rejection path.
This is the source decomposition `27 * 8 + 18`, proved from the executable
control flow rather than the static 1800 allowance. -/
theorem selected_semanticScript_logBound_234 (binding : Binding)
    (body : Bytes) (tape : Tape) :
    LogBound tape (semanticScript true binding body) 234 := by
  -- The remaining source-shaped composition is deliberately kept explicit;
  -- no 234-call premise is accepted from the caller.
  unfold semanticScript
  split
  · intro oracle
    rw [run_pad]
    simp only [run]
    omega
  · rename_i wire parsed
    dsimp only
    rw [show (234 : Nat) = 1 + 233 by decide]
    apply logBound_bind tape _ _ (optionalProfileScript_logBound tape true zeroDigest)
    intro afterPositive
    rw [show (233 : Nat) = 1 + 232 by decide]
    apply logBound_bind tape _ _
      (absorbScript_logBound tape afterPositive 1 selectedProfile)
    intro afterProfile
    rw [show (232 : Nat) = 1 + 231 by decide]
    apply logBound_bind tape _ _
      (absorbScript_logBound tape afterProfile 2 (List.ofFn binding))
    intro afterStatement
    rw [show (231 : Nat) = 1 + 230 by decide]
    apply logBound_bind tape _ _
      (absorbScript_logBound tape afterStatement 3 (List.ofFn (wire.roots 0)))
    intro afterC1
    rw [show (230 : Nat) = 8 + 222 by decide]
    apply logBound_bind tape _ _ (candidateScript_logBound tape afterC1)
    intro lambdaDraw
    cases lambdaDraw.1 with
    | error error =>
      exact logBound_done_cost tape
        (Except.error (FSLiveSemanticPrefix.Error.lambda error)) 222
    | ok lambda =>
      rw [show (222 : Nat) = 8 + 214 by decide]
      apply logBound_bind tape _ _ (candidateScript_logBound tape lambdaDraw.2)
      intro chiDraw
      cases chiDraw.1 with
      | error error =>
        exact logBound_done_cost tape
          (Except.error (FSLiveSemanticPrefix.Error.chi error)) 214
      | ok chi =>
        rw [show (214 : Nat) = 1 + 213 by decide]
        apply logBound_bind tape _ _
          (absorbScript_logBound tape chiDraw.2 9 (List.ofFn (wire.roots 1)))
        intro afterC2
        rw [show (213 : Nat) = 1 + 212 by decide]
        apply logBound_bind tape _ _
          (absorbScript_logBound tape afterC2 32 constraintRegistry)
        intro afterRegistry
        rw [show (212 : Nat) = 1 + 211 by decide]
        apply logBound_bind tape _ _
          (absorbScript_logBound tape afterRegistry 33 helperZero)
        intro afterHelper
        rw [show (211 : Nat) = 96 + 115 by decide]
        apply logBound_bind tape _ _
          (indexedCandidates_logBound tape 12 0 afterHelper)
        intro batchDraw
        cases batchDraw.1 with
        | error error =>
          exact logBound_done_cost tape
            (Except.error
              (FSLiveSemanticPrefix.Error.batching error.1 error.2)) 115
        | ok batchValues =>
          let initial := wire.values.getD 0 0
          rw [show (115 : Nat) = 1 + 114 by decide]
          apply logBound_bind tape _ _
            (absorbScript_logBound tape batchDraw.2 31 (maskClaimRecord initial))
          intro afterMask
          rw [show (114 : Nat) = 24 + 90 by decide]
          apply logBound_bind tape _ _ (nonzeroScript_logBound tape 3 afterMask)
          intro etaDraw
          cases etaDraw.1 with
          | error error =>
            exact logBound_done_cost tape
              (Except.error (FSLiveSemanticPrefix.Error.eta error)) 90
          | ok eta =>
            rw [show (90 : Nat) = 90 + 0 by decide]
            apply logBound_bind tape _ _
              (semanticRounds_logBound tape body wire.values 10 0 initial etaDraw.2)
            intro rounds
            exact logBound_done tape
              (match rounds with
              | Except.error (r, e) => Except.error
                  (FSLiveSemanticPrefix.Error.semanticRound r e)
              | Except.ok state => Except.ok
                  (FSLiveSemanticPrefix.Success.mk lambda chi
                    (batchingOfList batchValues).theta
                    (batchingOfList batchValues).zc
                    (batchingOfList batchValues).mu eta
                    (tenCoordinates state.z) state.claim state.digest))

theorem selected_semanticScript_log_length_le_234 (binding : Binding)
    (body : Bytes) (tape : Tape) (oracle : Oracle) :
    (run tape (semanticScript true binding body) oracle).2.log.length ≤
      oracle.log.length + 234 :=
  selected_semanticScript_logBound_234 binding body tape oracle

#print axioms selected_semanticScript_logBound_234
#print axioms selected_semanticScript_log_length_le_234

end AspisV8Completion.S8SemanticPathBudget
