import R1C1PartialCandidates
import R0P.SemPad

/-! Exact identification of the C1 lane projection with the old C2 zero
padding. This is a finite representation equality and adds no semantic or
security premise. -/
set_option autoImplicit false

namespace AspisR1.C1SemanticPadding

open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]
  {Sfield : Fin 29 → Subfield K}

private theorem old_padWord_eq_zero : R0P.SemSource.padWord = (0 : InitialWord K) := by
  change exactInitialEncoder (fun _ => 0) = (0 : InitialWord K)
  exact AspisR1.PartialJointList.exactInitialEncoder_zero

theorem projectWord_eq_c2Words (x : R0P.SemSource.TypedContext K Sfield) :
    AspisR1.PartialJointList.projectWord AspisR1.C1PartialCandidates.c1Lanes x.W =
      R0P.SemSource.c2Words x R0P.SemSource.padWord R0P.SemSource.padWord := by
  funext lane
  by_cases hmem : lane ∈ AspisR1.C1PartialCandidates.c1Lanes
  · have hcases := (AspisR1.C1PartialCandidates.mem_c1Lanes lane).mp hmem
    rcases hcases with hlt | h28
    · have h26 : lane ≠ 26 := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      have h27 : lane ≠ 27 := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      simp [AspisR1.PartialJointList.projectWord, hmem,
        R0P.SemSource.c2Words, h26, h27]
    · have h26 : lane ≠ 26 := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      have h27 : lane ≠ 27 := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      simp [AspisR1.PartialJointList.projectWord, hmem,
        R0P.SemSource.c2Words, h26, h27]
  · have hnot : ¬ (lane.val < 26 ∨ lane.val = 28) := by
      intro hv
      apply hmem
      exact (AspisR1.C1PartialCandidates.mem_c1Lanes lane).mpr hv
    have hval : lane.val = 26 ∨ lane.val = 27 := by omega
    rcases hval with h26 | h27
    · have heq : lane = 26 := Fin.ext h26
      subst lane
      simp [AspisR1.PartialJointList.projectWord, hmem,
        R0P.SemSource.c2Words, old_padWord_eq_zero]
    · have heq : lane = 27 := Fin.ext h27
      subst lane
      simp [AspisR1.PartialJointList.projectWord, hmem,
        R0P.SemSource.c2Words, old_padWord_eq_zero]

theorem candidates_eq_old_Lambda (x : R0P.SemSource.TypedContext K Sfield) :
    AspisR1.C1PartialCandidates.candidates x.W =
      AspisR0.ListsResponses.Lambda
        (R0P.SemSource.c2Words x R0P.SemSource.padWord R0P.SemSource.padWord) := by
  unfold AspisR1.C1PartialCandidates.candidates
  rw [projectWord_eq_c2Words]
  rfl

#print axioms projectWord_eq_c2Words
#print axioms candidates_eq_old_Lambda

end AspisR1.C1SemanticPadding
