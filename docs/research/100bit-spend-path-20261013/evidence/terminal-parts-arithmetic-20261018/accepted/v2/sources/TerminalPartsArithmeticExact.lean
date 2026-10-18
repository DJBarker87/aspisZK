import EqualityValueLoop

/-! Exact arithmetic of the source `terminal_parts` suffix, after its
composition call has returned. This retains the actual selected-carrier
operations and reuses the checked equality-value loop. The composition call,
public wrapper and production-source instantiation remain separate. -/
set_option autoImplicit false
namespace AspisR1.TerminalPartsArithmeticExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Arr := Array QM 10#usize
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

/-- Source arithmetic sequence, with the already-unwrapped composition
result supplied explicitly. No field operation is replaced by its model. -/
def run (zerocheck_point point : Arr) (composition h1_z copy_active mu : QM) :
    Result QM := do
  let q ← pool_v1.pair_forest_semantic_terminal.equality_value zerocheck_point point
  let q1 ← field.QM31.mul q composition
  let q2 ← field.QM31.mul mu h1_z
  let q3 ← field.QM31.add q1 q2
  let q4 ← field.QM31.mul mu mu
  let q5 ← field.QM31.sub field.QM31.ONE copy_active
  let q6 ← field.QM31.mul q5 h1_z
  let q7 ← field.QM31.mul q4 q6
  field.QM31.add q3 q7

theorem run_exact (zerocheck_point point : Arr)
    (composition h1_z copy_active mu : QM)
    (hzc : ∀ i : Fin 10, Canonical
      (zerocheck_point.val[i.val]'(by simpa [zerocheck_point.property] using i.isLt)))
    (hpoint : ∀ i : Fin 10, Canonical
      (point.val[i.val]'(by simpa [point.property] using i.isLt)))
    (hc : Canonical composition) (hh : Canonical h1_z)
    (ha : Canonical copy_active) (hm : Canonical mu) :
    ∃ out, run zerocheck_point point composition h1_z copy_active mu = ok out ∧
      Canonical out ∧
      decode out =
        R0P.SemSource.eqValue
          (AspisR1.EqualityValueLoop.decodedArray zerocheck_point)
          (AspisR1.EqualityValueLoop.decodedArray point) * decode composition +
        decode mu * decode h1_z +
        (decode mu * decode mu) * ((1 - decode copy_active) * decode h1_z) := by
  obtain ⟨q, hq, cq, vq⟩ :=
    AspisR1.EqualityValueLoop.equality_value_success zerocheck_point point hzc hpoint
  obtain ⟨q1, hq1, cq1, vq1⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q composition cq hc
  obtain ⟨q2, hq2, cq2, vq2⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact mu h1_z hm hh
  obtain ⟨q3, hq3, cq3, vq3⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q1 q2 cq1 cq2
  obtain ⟨q4, hq4, cq4, vq4⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact mu mu hm hm
  obtain ⟨q5, hq5, cq5, vq5⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact field.QM31.ONE copy_active
      AspisR1.ExtractedMaskConstants.one_canonical ha
  obtain ⟨q6, hq6, cq6, vq6⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q5 h1_z cq5 hh
  obtain ⟨q7, hq7, cq7, vq7⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q4 q6 cq4 cq6
  obtain ⟨out, hout, cout, vout⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q3 q7 cq3 cq7
  refine ⟨out, ?_, cout, ?_⟩
  · simp only [run, hq, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hout, bind_tc_ok]
  · simp only [decode, AspisR1.EqualityValueAdapter.decode] at vq vq5 ⊢
    rw [vout, vq3, vq1, vq2, vq7, vq4, vq6, vq5,
      AspisR1.ExtractedMaskConstants.one_decode, vq]

#print axioms run_exact
end AspisR1.TerminalPartsArithmeticExact
