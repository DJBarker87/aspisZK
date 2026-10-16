import EqualityValueAdapter
import ExtractedMaskConstants

/-!
Scalar arithmetic slice for the generated `terminal_parts` body.  The
composition-array and equality-value sources are exposed as separate input
contracts; this theorem does not identify either result with the R0P lane
model.  It only proves the final source arithmetic once those components have
returned canonical QM31 values.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskTerminalArithmetic
open Aeneas.Std Result

abbrev QM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
def terminalFormula (q composition h1 active mu : ExactQM) : ExactQM :=
  q * composition + mu * h1 + mu * mu * ((1 - active) * h1)

/-- The successive generated terminal arithmetic calls succeed and their
exact decoded result is the displayed scalar formula.  This is the reusable
component-level adapter consumed after separate proofs identify `q`,
`composition`, `h1`, and `active` with their semantic models. -/
theorem terminal_scalar_calls
    (q composition h1 active mu : QM)
    (hq : Canonical q) (hcomposition : Canonical composition)
    (hh1 : Canonical h1) (hactive : Canonical active) (hmu : Canonical mu) :
    ∃ out : QM,
      (∃ q1 q2 q3 q4 q5 q6 q7 : QM,
        AspisR1SelectedMaskProbe.field.QM31.mul q composition = .ok q1 ∧
        AspisR1SelectedMaskProbe.field.QM31.mul mu h1 = .ok q2 ∧
        AspisR1SelectedMaskProbe.field.QM31.add q1 q2 = .ok q3 ∧
        AspisR1SelectedMaskProbe.field.QM31.mul mu mu = .ok q4 ∧
        AspisR1SelectedMaskProbe.field.QM31.sub
          AspisR1SelectedMaskProbe.field.QM31.ONE active = .ok q5 ∧
        AspisR1SelectedMaskProbe.field.QM31.mul q5 h1 = .ok q6 ∧
        AspisR1SelectedMaskProbe.field.QM31.mul q4 q6 = .ok q7 ∧
        AspisR1SelectedMaskProbe.field.QM31.add q3 q7 = .ok out) ∧
      Canonical out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        terminalFormula
          (AspisR1.ExtractedMaskQM31Exact.decode q)
          (AspisR1.ExtractedMaskQM31Exact.decode composition)
          (AspisR1.ExtractedMaskQM31Exact.decode h1)
          (AspisR1.ExtractedMaskQM31Exact.decode active)
          (AspisR1.ExtractedMaskQM31Exact.decode mu) := by
  obtain ⟨q1, hq1, hq1c, hq1v⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q composition
      hq hcomposition
  obtain ⟨q2, hq2, hq2c, hq2v⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact mu h1 hmu hh1
  obtain ⟨q3, hq3, hq3c, hq3v⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q1 q2 hq1c hq2c
  obtain ⟨q4, hq4, hq4c, hq4v⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact mu mu hmu hmu
  obtain ⟨q5, hq5, hq5c, hq5v⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact
      AspisR1SelectedMaskProbe.field.QM31.ONE active
      AspisR1.ExtractedMaskConstants.one_canonical hactive
  obtain ⟨q6, hq6, hq6c, hq6v⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q5 h1 hq5c hh1
  obtain ⟨q7, hq7, hq7c, hq7v⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q4 q6 hq4c hq6c
  obtain ⟨out, hout, houtc, houtv⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q3 q7 hq3c hq7c
  refine ⟨out, ⟨q1, q2, q3, q4, q5, q6, q7,
    hq1, hq2, hq3, hq4, hq5, hq6, hq7, hout⟩, houtc, ?_⟩
  have hq5v' : AspisR1.ExtractedMaskQM31Exact.decode q5 =
      AspisR1.ExtractedMaskQM31Exact.decode AspisR1SelectedMaskProbe.field.QM31.ONE -
        AspisR1.ExtractedMaskQM31Exact.decode active := by
    simpa only [AspisR1.EqualityValueAdapter.decode] using hq5v
  rw [houtv, hq3v, hq1v, hq2v, hq7v, hq4v, hq6v, hq5v']
  rw [AspisR1.ExtractedMaskConstants.one_decode]
  simp only [AspisR1.ExtractedMaskQM31Exact.decode, terminalFormula]

#print axioms terminal_scalar_calls

end AspisR1.ExtractedMaskTerminalArithmetic
