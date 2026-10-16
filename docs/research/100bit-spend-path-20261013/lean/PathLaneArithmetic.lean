import EqualityValueAdapter
import ExtractedMaskQM31Exact
import ExtractedMaskConstants

/-! The literal path constraints' checked operation chains. These lemmas
retain the exact association and source calls; neither field success nor a
residual equality is supplied as a premise. -/
set_option autoImplicit false
namespace AspisR1.PathLaneArithmetic
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskConstants

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM

def booleanResidual (selector bit : QM) : Result QM := do
  let q ← field.QM31.sub bit field.QM31.ONE
  let q1 ← field.QM31.mul bit q
  field.QM31.mul selector q1

def pathPair (selector bit current left right : QM) : Result (QM × QM) := do
  let q ← field.QM31.sub field.QM31.ONE bit
  let q1 ← field.QM31.mul selector q
  let q3 ← field.QM31.sub left current
  let q4 ← field.QM31.mul q1 q3
  let q5 ← field.QM31.mul selector bit
  let q7 ← field.QM31.sub right current
  let q8 ← field.QM31.mul q5 q7
  .ok (q4, q8)

theorem booleanResidual_success (selector bit : QM)
    (hs : Canonical selector) (hb : Canonical bit) :
    ∃ out, booleanResidual selector bit = .ok out ∧ Canonical out ∧
      decode out = decode selector * (decode bit * (decode bit - 1)) := by
  obtain ⟨q, hq, hcq, hvq⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact bit field.QM31.ONE hb one_canonical
  obtain ⟨q1, hq1, hcq1, hvq1⟩ := current_qm_mul_exact bit q hb hcq
  obtain ⟨out, hout, hcout, hvout⟩ := current_qm_mul_exact selector q1 hs hcq1
  refine ⟨out, ?_, hcout, ?_⟩
  · simp only [booleanResidual, hq, bind_tc_ok, hq1, hout]
  · change decode q = decode bit - decode field.QM31.ONE at hvq
    rw [hvout, hvq1, hvq, one_decode]

theorem pathPair_success (selector bit current left right : QM)
    (hs : Canonical selector) (hb : Canonical bit)
    (hc : Canonical current) (hl : Canonical left) (hr : Canonical right) :
    ∃ outLeft outRight,
      pathPair selector bit current left right = .ok (outLeft, outRight) ∧
      Canonical outLeft ∧ Canonical outRight ∧
      decode outLeft = decode selector * (1 - decode bit) * (decode left - decode current) ∧
      decode outRight = decode selector * decode bit * (decode right - decode current) := by
  obtain ⟨q, hq, hcq, hvq⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact field.QM31.ONE bit one_canonical hb
  obtain ⟨q1, hq1, hcq1, hvq1⟩ := current_qm_mul_exact selector q hs hcq
  obtain ⟨q3, hq3, hcq3, hvq3⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact left current hl hc
  obtain ⟨q4, hq4, hcq4, hvq4⟩ := current_qm_mul_exact q1 q3 hcq1 hcq3
  obtain ⟨q5, hq5, hcq5, hvq5⟩ := current_qm_mul_exact selector bit hs hb
  obtain ⟨q7, hq7, hcq7, hvq7⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact right current hr hc
  obtain ⟨q8, hq8, hcq8, hvq8⟩ := current_qm_mul_exact q5 q7 hcq5 hcq7
  refine ⟨q4, q8, ?_, hcq4, hcq8, ?_, ?_⟩
  · simp only [pathPair, hq, bind_tc_ok, hq1, hq3, hq4, hq5, hq7, hq8]
  · change decode q = decode field.QM31.ONE - decode bit at hvq
    change decode q3 = decode left - decode current at hvq3
    rw [hvq4, hvq1, hvq, one_decode, hvq3]
  · change decode q7 = decode right - decode current at hvq7
    rw [hvq8, hvq5, hvq7]

#print axioms booleanResidual_success
#print axioms pathPair_success
end AspisR1.PathLaneArithmetic
