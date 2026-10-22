import S9SelectedHelperCorrectResultV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9SelectedHelperTopCorrectResultV1

open AspisR1S9HelperP6

local instance selectedOps : FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev U := Std.Usize
abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev cells (a : W) (j : Fin 4) := AspisR1.S9ArrayWriteScheduleRootV1.cells a j
abbrev TraceDecode := AspisR1S9SelectedHelperCorrectResultV1.TraceDecode
abbrev ScaledBase := AspisR1S9SelectedHelperCorrectResultV1.ScaledBase
abbrev Seed := AspisR1S9SelectedHelperCorrectResultV1.Seed

/-- The public selected-model helper wrapper is exactly the zero-initialized
loop, so the constructive loop result gives its full canonical and coefficient
postcondition without a loop-success premise. -/
theorem selected_helper_top_correct_result
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (hap0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → Canonical x)
    (hap1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → Canonical x)
    (hextra : ∀ (j : U) (q : Q), Array.index_usize extra j = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q)) :
    ∃ output q0 q1,
      weights.factored_s2_libra_weights ap0 ap1 extra = .ok output ∧
      Array.index_usize extra 0#usize = .ok q0 ∧
      Array.index_usize extra 1#usize = .ok q1 ∧
      (∀ j : Fin 4, Canonical (cells output j)) ∧
      (∀ j : Fin 4,
        TraceDecode (cells output j) =
          AspisR1.S2LibraFactoredIdentity.original
            (ScaledBase ap0) (ScaledBase ap1) (Seed q0) (Seed q1) j) := by
  obtain ⟨output, q0, q1, hloop, hq0, hq1, hcanonical, hcoeff⟩ :=
    AspisR1S9SelectedHelperCorrectResultV1.selected_helper_correct_result
      ap0 ap1 extra hap0 hap1 hextra
  refine ⟨output, q0, q1, ?_, hq0, hq1, hcanonical, hcoeff⟩
  simpa only [weights.factored_s2_libra_weights, AspisR1S9FactoredLoopTwoStepV4.start0, bind_tc_ok] using hloop

#print axioms selected_helper_top_correct_result

end AspisR1S9SelectedHelperTopCorrectResultV1
