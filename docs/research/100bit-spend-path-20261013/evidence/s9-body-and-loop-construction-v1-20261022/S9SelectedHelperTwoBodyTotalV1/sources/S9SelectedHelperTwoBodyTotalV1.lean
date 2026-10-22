import S9SideZeroActiveBodyTotalityV1
import S9SideOneActiveBodyTotalityV1
import S9ForwardLoopConstructorV1
import S9FixedIteratorTransitionsV1
import S9HighTermSourceCellRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9SelectedHelperTwoBodyTotalV1

open AspisR1S9HelperP6
local instance selectedOps : FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical

/-- The fixed two-step helper loop succeeds from canonical source arrays.
The second call receives the exact first-call output, and its slot-one
canonicality is transported from the first branch's checked array output. -/
theorem selected_helper_total
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (initial : W)
    (hap0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → Canonical x)
    (hap1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → Canonical x)
    (hextra : ∀ (j : U) (q : Q), Array.index_usize extra j = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q)) :
    ∃ output,
      weights.factored_s2_libra_weights_loop
        AspisR1S9FactoredLoopTwoStepV4.start0 ap0 ap1 extra initial = .ok output := by
  obtain ⟨middle, hbody0, hmiddle0, hmiddle1⟩ :=
    AspisR1S9SideZeroActiveBodyTotalityV1.side_zero_active_body_total
      ap0 ap1 extra AspisR1S9FactoredLoopTwoStepV4.start1 initial hap0 hap1 hextra
  have hmiddle1read : ∀ (x : field.WideExact),
      Array.index_usize middle 1#usize = .ok x → Canonical x := by
    intro x hx
    have hcell := AspisR1.S9HighTermPolynomialMeaningRootV1.source_read_cell
      middle 1#usize x (by decide) hx
    rw [← hcell]
    exact hmiddle1
  obtain ⟨output, hbody1, _houtput1, _houtput2, _houtput3⟩ :=
    AspisR1S9SideOneActiveBodyTotalityV1.side_one_active_body_total
      ap0 ap1 extra AspisR1S9FactoredLoopTwoStepV4.start2 middle
      hap0 hap1 hextra hmiddle1read
  have hn0 := AspisR1S9FixedIteratorTransitionsV1.next_start0
  have hn1 := AspisR1S9FixedIteratorTransitionsV1.next_start1
  have hn2 := AspisR1S9FixedIteratorTransitionsV1.next_start2
  exact ⟨output,
    AspisR1S9ForwardLoopConstructorV1.helper_loop_of_two_active_calls
      ap0 ap1 extra initial middle output
      AspisR1S9FactoredLoopTwoStepV4.start0
      AspisR1S9FactoredLoopTwoStepV4.start1
      AspisR1S9FactoredLoopTwoStepV4.start2
      0#usize 1#usize hn0 hn1 hn2 hbody0 hbody1⟩

#print axioms selected_helper_total

end AspisR1S9SelectedHelperTwoBodyTotalV1
