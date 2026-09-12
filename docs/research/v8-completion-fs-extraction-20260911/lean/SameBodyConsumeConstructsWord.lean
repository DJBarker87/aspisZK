import SameBodyAssembly
import Mathlib.Tactic

/-!
# Successful relation consumption reconstructs the same causal word

This leaf replaces a supplied whole-word equality by the equalities checked
by `SameBodyRelation.consume`.  It remains conditional on an actual successful
consumer run, which the chronological source verifier must construct.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 2000

namespace AspisV8Completion.SameBodyConsumeConstructsWord

open SameBodyRelation SameBodyAssembly

universe u v
variable {K : Type u} {Schedule : Type v}

/-- The canonical early/round/final projections reassemble any 697-field
word exactly. -/
theorem assemble_roundtrip (w : Word K) :
    assemble (early w) (fun round => response w round) (finalValues w) = w := by
  funext index
  unfold assemble
  split
  · rename_i earlyIndex
    simp [early]
  next notEarly =>
    split
    · rename_i relationIndex
      change w (responseIndex
        ⟨(index.val - 417) / 6, by omega⟩
        ⟨(index.val - 417) % 6, Nat.mod_lt _ (by decide)⟩) = w index
      congr 1
      apply Fin.ext
      simp only [responseIndex, Fin.val_mk]
      omega
    · change w (finalIndex ⟨index.val - 441, by omega⟩) = w index
      congr 1
      apply Fin.ext
      simp only [finalIndex, Fin.val_mk]
      omega

/-- A successful same-word consumer run constructs the previously explicit
`causalWord` equality.  No terminal acceptance or probability premise is
used. -/
theorem consume_success_constructs_word [DecidableEq K]
    (ops : Arithmetic K) (strategy : Strategy K Schedule) (w : Word K)
    (tau alpha : K) (queries : Schedule) (rho : K) (coins : Fin 3 → K)
    (ordinary : K) (increment : Final K → Schedule → K → K)
    (result : Result K)
    (success : consume ops strategy w tau alpha queries rho coins ordinary
      increment = some result) :
    w = produce (early w) strategy tau alpha queries rho coins := by
  have correspondence := consume_constructs_correspondence ops strategy w tau
    alpha queries rho coins ordinary increment result success
  let finalStage := (strategy tau).afterAlpha0 alpha
  generalize tailEq : finalStage.afterQueries queries rho = tail at correspondence
  cases tail with
  | round message1 next1 =>
    cases next1Eq : next1 (coins 0) with
    | round message2 next2 =>
      cases next2Eq : next2 (coins 1) with
      | round message3 next3 =>
        cases next3Eq : next3 (coins 2) with
        | done =>
          have later := correspondence.2.2.1
          simp only [tailMessages] at later
          rw [next1Eq] at later
          simp only [tailMessages] at later
          have next2Eq' : next2 (coins (Fin.succ 0)) =
              Tail.round message3 next3 := by simpa using next2Eq
          rw [next2Eq'] at later
          simp only [tailMessages] at later
          have next3Eq' : next3 (coins (Fin.succ (Fin.succ 0))) =
              Tail.done := by simpa using next3Eq
          rw [next3Eq'] at later
          simp only [tailMessages, laterResponses, List.cons.injEq] at later
          have rounds : roundsOfTail (strategy tau).response0
              (finalStage.afterQueries queries rho) coins =
                fun round => response w round := by
            rw [tailEq]
            change (match next1 (coins 0) with
              | .round second secondNext =>
                match secondNext (coins 1) with
                | .round third _ => fun round =>
                  if round.val = 0 then (strategy tau).response0
                  else if round.val = 1 then message1
                  else if round.val = 2 then second else third) =
                fun round => response w round
            rw [next1Eq]
            change (match next2 (coins 1) with
              | .round third _ => fun round =>
                if round.val = 0 then (strategy tau).response0
                else if round.val = 1 then message1
                else if round.val = 2 then message2 else third) =
                  fun round => response w round
            rw [next2Eq]
            funext round
            fin_cases round
            · simp [correspondence.1]
            · simp [later.1]
            · simp [later.2.1]
            · simp [later.2.2.1]
          have final : finalStage.final256 = finalValues w := correspondence.2.1
          symm
          change assemble (early w)
              (roundsOfTail (strategy tau).response0
                (finalStage.afterQueries queries rho) coins)
              finalStage.final256 = w
          rw [rounds, final]
          exact assemble_roundtrip w

#print axioms assemble_roundtrip
#print axioms consume_success_constructs_word

end AspisV8Completion.SameBodyConsumeConstructsWord
