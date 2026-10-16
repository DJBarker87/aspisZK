import EqualityValueAdapter
import ExtractedMaskQM31Exact
import SelectorExpansionCorrectness

/-! Concrete checked field-operation chain in the conservation tail of
add_value_lanes. Array reads and selector construction are separate caller
steps; no desired residual or operation-success equation is assumed. -/
set_option autoImplicit false
namespace AspisR1.ValueConservationArithmetic
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM

theorem conservation_success
    (selector z0 z1 z2 s0 s1 : QM)
    (hselector : Canonical selector)
    (hz0 : Canonical z0) (hz1 : Canonical z1) (hz2 : Canonical z2)
    (hs0 : Canonical s0) (hs1 : Canonical s1) :
    ∃ d01 d012 r0 ds r1 : QM,
      field.QM31.sub z0 z1 = .ok d01 ∧
      field.QM31.sub d01 z2 = .ok d012 ∧
      field.QM31.mul selector d012 = .ok r0 ∧
      field.QM31.sub s0 s1 = .ok ds ∧
      field.QM31.mul selector ds = .ok r1 ∧
      AspisR1.SelectorExpansionCorrectness.canonicalArray
        (Array.make 2#usize [r0, r1]) ∧
      decode r0 = decode selector * ((decode z0 - decode z1) - decode z2) ∧
      decode r1 = decode selector * (decode s0 - decode s1) := by
  obtain ⟨d01, hd01, hc01, hv01⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact z0 z1 hz0 hz1
  obtain ⟨d012, hd012, hc012, hv012⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact d01 z2 hc01 hz2
  obtain ⟨r0, hr0, hc0, hv0⟩ := current_qm_mul_exact selector d012 hselector hc012
  obtain ⟨ds, hds, hcs, hvs⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact s0 s1 hs0 hs1
  obtain ⟨r1, hr1, hc1, hv1⟩ := current_qm_mul_exact selector ds hselector hcs
  have harray : AspisR1.SelectorExpansionCorrectness.canonicalArray
      (Array.make 2#usize [r0, r1]) := by
    intro j
    fin_cases j
    · exact hc0
    · exact hc1
  refine ⟨d01, d012, r0, ds, r1, hd01, hd012, hr0, hds, hr1, harray, ?_, ?_⟩
  · change decode d01 = decode z0 - decode z1 at hv01
    change decode d012 = decode d01 - decode z2 at hv012
    rw [hv0, hv012, hv01]
  · change decode ds = decode s0 - decode s1 at hvs
    rw [hv1, hvs]

#print axioms conservation_success
end AspisR1.ValueConservationArithmetic
