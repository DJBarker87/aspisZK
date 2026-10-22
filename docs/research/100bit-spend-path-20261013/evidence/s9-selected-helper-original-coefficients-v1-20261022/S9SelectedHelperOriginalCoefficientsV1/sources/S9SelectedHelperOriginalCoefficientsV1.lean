import S9ActualTwoBodyCoefficientsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9SelectedHelperOriginalCoefficientsV10

open AspisR1S9HelperP6

abbrev W := AspisR1S9BodyPrefixSemanticsV1.W
abbrev Q := field.QM31
abbrev U := Std.Usize
abbrev TraceDecode := AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecode
abbrev ScaledBase := AspisR1S9BodyPrefixPolynomialSumsV1.ScaledBase
abbrev Seed := AspisR1S9BodyPrefixPolynomialSumsV1.Seed
abbrev cells (a : W) (j : Fin 4) := AspisR1.S9ArrayWriteScheduleRootV1.cells a j

/-- One successful selected helper execution, under the same selected-model
canonical read premises, returns challenges read from the actual extra array
and all four output coefficients equal the original 56-coefficient S2 form.
This is still a selected-model result; it does not add Rust `from_fn` or caller
source correspondence. -/
theorem successful_selected_helper_has_original_coefficients
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (initial output : W)
    (hloop : weights.factored_s2_libra_weights_loop
      AspisR1S9FactoredLoopTwoStepV4.start0 ap0 ap1 extra initial = .ok output)
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hextra : ∀ (j : U) (x : Q), Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x) :
    ∃ q0 q1 : Q,
      Array.index_usize extra 0#usize = .ok q0 ∧
      Array.index_usize extra 1#usize = .ok q1 ∧
      ∀ j : Fin 4,
        TraceDecode (cells output j) =
          AspisR1.S2LibraFactoredIdentity.original
            (ScaledBase ap0) (ScaledBase ap1) (Seed q0) (Seed q1) j := by
  obtain ⟨iter1, iter2, middle, hw⟩ :=
    AspisR1S9ActualTwoBodyCompositionV1.successful_helper_has_two_body_witnesses
      ap0 ap1 extra initial output hloop hp0 hp1 hextra
  obtain ⟨w⟩ := hw
  let q0 := w.sideZero.execution.q
  let q1 := w.sideOne.prefixData.q
  have hq0 : Array.index_usize extra 0#usize = .ok q0 := w.sideZero.execution.hq
  have hq1 : Array.index_usize extra 1#usize = .ok q1 := w.sideOne.prefixData.hq
  refine ⟨q0, q1, hq0, hq1, ?_⟩
  intro j
  have hfact := AspisR1S9ActualTwoBodyCoefficientsV17.two_body_output_factored
    ap0 ap1 extra initial middle output iter1 iter2 w j
  exact hfact.trans
    (AspisR1.S2LibraFactoredIdentity.original_eq_factored
      (ScaledBase ap0) (ScaledBase ap1) (Seed q0) (Seed q1) j).symm

#print axioms successful_selected_helper_has_original_coefficients

end AspisR1S9SelectedHelperOriginalCoefficientsV10
