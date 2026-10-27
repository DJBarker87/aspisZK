import R1Z.ProverCommitQuotientLaw
import R1Z.ProverCommitSectionObstruction

set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTapeCompletion
open R0Z.JointView
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K] [Fintype K] {F : Subfield K}

/-- A deterministic section satisfies the quotient law but fails every full law. -/
theorem quotient_law_strict (choose : SourceTape K F → Padding K F) :
    (∀ s : SourceTape K F, (Finset.univ.filter (fun i : SourceTape K F =>
      quotientDecode (fun q => some (complete q (choose q))) i = some s)).card = 1) ∧
    ¬ ∃ c : ℕ, ∀ t : Tape K F, (Finset.univ.filter (fun i : SourceTape K F =>
      some (complete i (choose i)) = some t)).card = c := by
  constructor
  · intro s
    have eq : (Finset.univ.filter (fun i : SourceTape K F =>
        quotientDecode (fun q => some (complete q (choose q))) i = some s)) = {s} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, quotientDecode,
        Option.map_some, project_complete, Option.some.injEq, Finset.mem_singleton]
    rw [eq, Finset.card_singleton]
  · simpa only [Option.some.injEq] using
      deterministic_section_not_equal_fibres choose (0, 0)

#print axioms quotient_law_strict
end R1Z.ProverCommitTapeCompletion
