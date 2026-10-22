import S9SelectedHelperTwoBodyTotalV1
import S9SelectedOutputCanonicalV1
import S9SelectedHelperOriginalCoefficientsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9SelectedHelperCorrectResultV1

open AspisR1S9HelperP6
local instance selectedOps : FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev U := Std.Usize
abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev cells (a : W) (j : Fin 4) := AspisR1.S9ArrayWriteScheduleRootV1.cells a j
abbrev TraceDecode := AspisR1S9SelectedHelperOriginalCoefficientsV10.TraceDecode
abbrev ScaledBase := AspisR1S9SelectedHelperOriginalCoefficientsV10.ScaledBase
abbrev Seed := AspisR1S9SelectedHelperOriginalCoefficientsV10.Seed

/-- Canonical source reads alone yield one selected helper result whose four
cells are canonical and whose actual challenge reads give the original S2
coefficient vector. -/
theorem selected_helper_correct_result
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (hap0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → Canonical x)
    (hap1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → Canonical x)
    (hextra : ∀ (j : U) (q : Q), Array.index_usize extra j = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q)) :
    ∃ output q0 q1,
      weights.factored_s2_libra_weights_loop
        AspisR1S9FactoredLoopTwoStepV4.start0 ap0 ap1 extra
        (Array.repeat 4#usize field.WideExact.ZERO) = .ok output ∧
      Array.index_usize extra 0#usize = .ok q0 ∧
      Array.index_usize extra 1#usize = .ok q1 ∧
      (∀ j : Fin 4, Canonical (cells output j)) ∧
      (∀ j : Fin 4,
        TraceDecode (cells output j) =
          AspisR1.S2LibraFactoredIdentity.original
            (ScaledBase ap0) (ScaledBase ap1) (Seed q0) (Seed q1) j) := by
  let initial : W := Array.repeat 4#usize field.WideExact.ZERO
  obtain ⟨output, hloop⟩ :=
    AspisR1S9SelectedHelperTwoBodyTotalV1.selected_helper_total
      ap0 ap1 extra initial hap0 hap1 hextra
  have hcanonical :=
    AspisR1S9SelectedOutputCanonicalV1.successful_selected_helper_output_all_canonical
      ap0 ap1 extra initial output hloop hap0 hap1 hextra
  obtain ⟨q0, q1, hq0, hq1, hcoeff⟩ :=
    AspisR1S9SelectedHelperOriginalCoefficientsV10.successful_selected_helper_has_original_coefficients
      ap0 ap1 extra initial output hloop hap0 hap1 hextra
  exact ⟨output, q0, q1, by simpa [initial] using hloop,
    hq0, hq1, hcanonical, hcoeff⟩

#print axioms selected_helper_correct_result

end AspisR1S9SelectedHelperCorrectResultV1
