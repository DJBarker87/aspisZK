import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4TerminalPartsArithmeticJoinChunk13V2
import ExtractedMaskQM31Exact
import EqualityValueAdapter
import ExtractedMaskConstants

open Aeneas Aeneas.Std Result
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticTail

abbrev QM := field.QM31
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

def run (q composition h1Z copyActive mu : QM) : Result QM := do
  let q1 ← field.QM31.mul q composition
  let q2 ← field.QM31.mul mu h1Z
  let q3 ← field.QM31.add q1 q2
  let q4 ← field.QM31.mul mu mu
  let q5 ← field.QM31.sub field.QM31.ONE copyActive
  let q6 ← field.QM31.mul q5 h1Z
  let q7 ← field.QM31.mul q4 q6
  field.QM31.add q3 q7

theorem run_exact (q composition h1Z copyActive mu : QM)
    (hq : Canonical q) (hc : Canonical composition)
    (hh : Canonical h1Z) (ha : Canonical copyActive) (hm : Canonical mu) :
    ∃ out, run q composition h1Z copyActive mu = .ok out ∧
      Canonical out ∧
      decode out =
        (decode q * decode composition + decode mu * decode h1Z) +
        (decode mu * decode mu) * ((1 - decode copyActive) * decode h1Z) := by
  obtain ⟨q1, hq1, hc1, vq1⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q composition hq hc
  obtain ⟨q2, hq2, hc2, vq2⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact mu h1Z hm hh
  obtain ⟨q3, hq3, hc3, vq3⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q1 q2 hc1 hc2
  obtain ⟨q4, hq4, hc4, vq4⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact mu mu hm hm
  obtain ⟨q5, hq5, hc5, vq5⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact field.QM31.ONE copyActive
      AspisR1.ExtractedMaskConstants.one_canonical ha
  obtain ⟨q6, hq6, hc6, vq6⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q5 h1Z hc5 hh
  obtain ⟨q7, hq7, hc7, vq7⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q4 q6 hc4 hc6
  obtain ⟨out, hout, hcout, vout⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q3 q7 hc3 hc7
  refine ⟨out, ?_, hcout, ?_⟩
  · simp only [run, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hout, bind_tc_ok]
  · rw [vout, vq3, vq1, vq2, vq7, vq4, vq6, vq5]
    simp [AspisR1.ExtractedMaskConstants.one_decode]

#print axioms run_exact
end AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticTail
