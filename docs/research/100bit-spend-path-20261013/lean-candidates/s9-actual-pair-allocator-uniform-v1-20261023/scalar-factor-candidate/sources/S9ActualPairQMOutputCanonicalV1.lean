import S9ActualPairSquareHelperTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairQMOutputCanonicalV1
abbrev Q := aspis_core.field.QM31
abbrev Canonical := AspisR1S9ActualPairQMHelperTransportV1.Canonical

theorem one_canonical : Canonical aspis_core.field.QM31.ONE := by
  unfold aspis_core.field.QM31.ONE
  change (1 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647)
  decide

theorem square_success_canonical (x z : Q) (hx : Canonical x)
    (h : aspis_core.field.QM31.square x = .ok z) : Canonical z := by
  have hsource := AspisR1S9ActualPairSquareSourceMapV1.qm_square_map x
  rw [h] at hsource
  have hcut : AspisR1S9SquareMulQMCutV1.field.QM31.square
      (AspisR1S9ActualPairSquareSourceMapV1.toActualQM x) =
      .ok (AspisR1S9ActualPairSquareSourceMapV1.toActualQM z) := hsource.symm
  have hmap := AspisR1S9QMSquareCombinedSelectedV1.qm_square_maps_to_selected
    (AspisR1S9ActualPairSquareSourceMapV1.toActualQM x) hx
  rw [hcut] at hmap
  have hselected : AspisR1SelectedMaskProbe.field.QM31.square
      (AspisR1S9QMSquareCombinedSelectedV1.toSelectedQM
        (AspisR1S9ActualPairSquareSourceMapV1.toActualQM x)) =
      .ok (AspisR1S9QMSquareCombinedSelectedV1.toSelectedQM
        (AspisR1S9ActualPairSquareSourceMapV1.toActualQM z)) := hmap.symm
  obtain ⟨out,hout,hcan,_⟩ := AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact
    (AspisR1S9QMSquareCombinedSelectedV1.toSelectedQM
      (AspisR1S9ActualPairSquareSourceMapV1.toActualQM x)) hx
  have heq := Result.ok.inj (hout.symm.trans hselected)
  rw [heq] at hcan
  exact hcan
#print axioms one_canonical
#print axioms square_success_canonical
end AspisR1S9ActualPairQMOutputCanonicalV1
