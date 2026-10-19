import R1NaturalProjection

/-! Finite, computable sparse-image filter for decoded final candidates. -/

set_option autoImplicit false

namespace AspisR1.SecondFoldSparseProjectionCore

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Keep a final candidate exactly when it is the sparse lift of its low
coefficient lane. -/
def projectSparseCandidate (a : Fin 256 → K) : Option (Fin 64 → K) :=
  let m := AspisR1.laneCoefficients 64 0 a
  if _ : a = AspisR1.sparseLift m then some m else none

/-- Apply the sparse-image test to a finite decoder output list. -/
def projectFinalCandidates
    (candidates : List (Fin 256 → K)) : List (Fin 64 → K) :=
  candidates.filterMap projectSparseCandidate

theorem projectSparseCandidate_eq_some_iff
    (a : Fin 256 → K) (m : Fin 64 → K) :
    projectSparseCandidate a = some m ↔ a = AspisR1.sparseLift m := by
  constructor
  · unfold projectSparseCandidate
    dsimp
    split
    · intro hresult
      simp only [Option.some.injEq] at hresult
      rename_i hsparse
      rw [hresult] at hsparse
      exact hsparse
    · simp
  · intro h
    subst a
    have hzero := AspisR1.laneCoefficients_sparseLift (n := 64) m
      (0 : Fin 4)
    have hlane : AspisR1.laneCoefficients 64 0 (AspisR1.sparseLift m) = m := by
      simpa using hzero
    simp [projectSparseCandidate, hlane]

theorem projectFinalCandidates_mem_iff
    (candidates : List (Fin 256 → K)) (m : Fin 64 → K) :
    m ∈ projectFinalCandidates candidates ↔
      ∃ a ∈ candidates, a = AspisR1.sparseLift m := by
  constructor
  · intro hm
    simp only [projectFinalCandidates, List.mem_filterMap] at hm
    rcases hm with ⟨a, ha, hresult⟩
    exact ⟨a, ha, (projectSparseCandidate_eq_some_iff a m).mp hresult⟩
  · rintro ⟨a, ha, h⟩
    apply List.mem_filterMap.mpr
    exact ⟨a, ha, (projectSparseCandidate_eq_some_iff a m).mpr h⟩

#print axioms projectSparseCandidate_eq_some_iff
#print axioms projectFinalCandidates_mem_iff

end AspisR1.SecondFoldSparseProjectionCore
