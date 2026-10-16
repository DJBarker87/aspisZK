import ScheduleDomainConstants
import ExtractedMaskQM31Exact
import ExtractedMaskScalarExact

/-! Actual source domain and length chains, using the retained current
scalar-multiplication theorem and source constants. -/
set_option autoImplicit false
namespace AspisR1.ScheduleDomainArithmetic
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskScalarExact
abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev owner := AspisR1ScheduleDomainCandidate.spend.DOMAIN_OWNER_KEY
abbrev note := AspisR1ScheduleDomainCandidate.spend.DOMAIN_NOTE
abbrev nullifier := AspisR1ScheduleDomainCandidate.spend.DOMAIN_NULLIFIER

theorem scalarEmbedding_nat (s : field.M31) :
    scalarEmbedding s = (s.val : ExactQM) := by
  ext <;> simp only [scalarEmbedding, AspisV8R15.ExactTowerBase.QM31Exact,
    AspisV8R15.ExactTowerBase.CM31Exact, QuadraticAlgebra.re_natCast,
    QuadraticAlgebra.im_natCast, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]

def run (h0 h1 h25 h30 transfer : QM) : Result (QM × QM) := do
  let q13 ← field.QM31.add h1 h30
  let first ← field.QM31.add q13 transfer
  let q14 ← field.QM31.mul_m31 h0 owner
  let q15 ← field.QM31.mul_m31 first note
  let q16 ← field.QM31.add q14 q15
  let q17 ← field.QM31.mul_m31 h25 nullifier
  let domain ← field.QM31.add q16 q17
  let q18 ← field.QM31.mul_m31 h0 8#u32
  let q19 ← field.QM31.mul_m31 first 18#u32
  let q20 ← field.QM31.add q18 q19
  let q21 ← field.QM31.mul_m31 h25 16#u32
  let length ← field.QM31.add q20 q21
  .ok (domain, length)

theorem source_success (h0 h1 h25 h30 transfer : QM)
    (hc1 : Canonical h1) (hc30 : Canonical h30) (hct : Canonical transfer) :
    ∃ domain length, run h0 h1 h25 h30 transfer = .ok (domain, length) ∧
      Canonical domain ∧ Canonical length ∧
      decode domain = (decode h0 * scalarEmbedding owner +
        ((decode h1 + decode h30) + decode transfer) * scalarEmbedding note) +
          decode h25 * scalarEmbedding nullifier ∧
      decode length = (decode h0 * scalarEmbedding 8#u32 +
        ((decode h1 + decode h30) + decode transfer) * scalarEmbedding 18#u32) +
          decode h25 * scalarEmbedding 16#u32 := by
  obtain ⟨q13, hr13, hc13, hv13⟩ := current_qm_add_exact h1 h30 hc1 hc30
  obtain ⟨first, hrfirst, hcfirst, hvfirst⟩ := current_qm_add_exact q13 transfer hc13 hct
  obtain ⟨q14, hr14, hc14, hv14⟩ := current_qm_mul_m31_exact h0 owner
  obtain ⟨q15, hr15, hc15, hv15⟩ := current_qm_mul_m31_exact first note
  obtain ⟨q16, hr16, hc16, hv16⟩ := current_qm_add_exact q14 q15 hc14 hc15
  obtain ⟨q17, hr17, hc17, hv17⟩ := current_qm_mul_m31_exact h25 nullifier
  obtain ⟨domain, hrdomain, hcdomain, hvdomain⟩ := current_qm_add_exact q16 q17 hc16 hc17
  obtain ⟨q18, hr18, hc18, hv18⟩ := current_qm_mul_m31_exact h0 8#u32
  obtain ⟨q19, hr19, hc19, hv19⟩ := current_qm_mul_m31_exact first 18#u32
  obtain ⟨q20, hr20, hc20, hv20⟩ := current_qm_add_exact q18 q19 hc18 hc19
  obtain ⟨q21, hr21, hc21, hv21⟩ := current_qm_mul_m31_exact h25 16#u32
  obtain ⟨length, hrlength, hclength, hvlength⟩ := current_qm_add_exact q20 q21 hc20 hc21
  refine ⟨domain, length, ?_, hcdomain, hclength, ?_, ?_⟩
  · simp only [run, hr13, bind_tc_ok, hrfirst, hr14, hr15, hr16, hr17,
      hrdomain, hr18, hr19, hr20, hr21, hrlength]
  · rw [hvdomain, hv16, hv14, hv15, hv17, hvfirst, hv13]
  · rw [hvlength, hv20, hv18, hv19, hv21, hvfirst, hv13]

#print axioms scalarEmbedding_nat
#print axioms source_success
end
end AspisR1.ScheduleDomainArithmetic
