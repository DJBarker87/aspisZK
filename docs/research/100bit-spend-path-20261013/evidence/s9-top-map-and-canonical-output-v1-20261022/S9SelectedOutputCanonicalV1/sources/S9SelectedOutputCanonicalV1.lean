import S9ActualTwoBodyCompositionV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9SelectedOutputCanonicalV1

open AspisR1S9HelperP6

abbrev W := AspisR1S9ActualTwoBodyCompositionV1.W
abbrev Q := AspisR1S9ActualTwoBodyCompositionV1.Q
abbrev U := AspisR1S9ActualTwoBodyCompositionV1.U
abbrev Canonical := AspisR1S9ActualTwoBodyCompositionV1.Canonical
abbrev cells (a : W) (j : Fin 4) := AspisR1.S9ArrayWriteScheduleRootV1.cells a j

/-- A successful selected-model helper run with the same canonical-read
premises returns four canonical cells. The first cell is preserved by the
side-one tail; the other three come from its checked output witness. -/
theorem successful_selected_helper_output_all_canonical
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (initial output : W)
    (hloop : weights.factored_s2_libra_weights_loop
      AspisR1S9FactoredLoopTwoStepV4.start0 ap0 ap1 extra initial = .ok output)
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → Canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → Canonical x)
    (hextra : ∀ (j : U) (x : Q), Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x) :
    ∀ j : Fin 4, Canonical (cells output j) := by
  obtain ⟨iter1, iter2, middle, hw⟩ :=
    AspisR1S9ActualTwoBodyCompositionV1.successful_helper_has_two_body_witnesses
      ap0 ap1 extra initial output hloop hp0 hp1 hextra
  obtain ⟨w⟩ := hw
  intro j
  fin_cases j
  · exact w.output0Canonical
  · exact w.sideOne.output1Canonical
  · exact w.sideOne.output2Canonical
  · exact w.sideOne.output3Canonical

#print axioms successful_selected_helper_output_all_canonical

end AspisR1S9SelectedOutputCanonicalV1
