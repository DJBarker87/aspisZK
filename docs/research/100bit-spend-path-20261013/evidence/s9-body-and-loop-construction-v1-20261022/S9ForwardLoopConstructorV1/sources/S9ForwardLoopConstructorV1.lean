import S9FactoredLoopTwoStepV4
import S9FactoredLoopBodyShapeV3

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ForwardLoopConstructorV1
open AspisR1S9HelperP6
abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev W := Array field.WideExact (4#usize)
variable [FieldOps]

/-- Constructs the actual helper loop result from its two active executions
and the actual iterator transitions, rather than assuming loop success. -/
theorem helper_loop_of_two_active_calls
    (ap0 ap1 : W) (extra : Array field.QM31 (2#usize))
    (initial middle output : W) (iter0 iter1 iter2 : R)
    (side0 side1 : U)
    (hn0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter0 =
      .ok (some side0,iter1))
    (hn1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter1 =
      .ok (some side1,iter2))
    (hn2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter2 =
      .ok (none,iter2))
    (ha0 : AspisR1S9FactoredLoopBodyShapeV3.activeBody ap0 ap1 extra side0 iter1 initial =
      .ok (.cont (iter1,middle)))
    (ha1 : AspisR1S9FactoredLoopBodyShapeV3.activeBody ap0 ap1 extra side1 iter2 middle =
      .ok (.cont (iter2,output))) :
    weights.factored_s2_libra_weights_loop iter0 ap0 ap1 extra initial = .ok output := by
  have hb0 := (AspisR1S9FactoredLoopBodyShapeV3.body_some_eq_activeBody
    ap0 ap1 extra iter0 iter1 side0 initial hn0).trans ha0
  have hb1 := (AspisR1S9FactoredLoopBodyShapeV3.body_some_eq_activeBody
    ap0 ap1 extra iter1 iter2 side1 middle hn1).trans ha1
  have hb2 : AspisR1S9FactoredLoopBodyShapeV3.body ap0 ap1 extra
      (iter2,output) = .ok (.done output) := by
    unfold AspisR1S9FactoredLoopBodyShapeV3.body
      weights.factored_s2_libra_weights_loop.body
    rw [hn2]
    rfl
  have hloop : Aeneas.Std.loop (AspisR1S9FactoredLoopBodyShapeV3.body ap0 ap1 extra)
      (iter0,initial) = .ok output := by
    rw [Aeneas.Std.loop.eq_def,hb0]
    dsimp only
    rw [Aeneas.Std.loop.eq_def,hb1]
    dsimp only
    rw [Aeneas.Std.loop.eq_def,hb2]
  unfold weights.factored_s2_libra_weights_loop
  exact hloop

#print axioms helper_loop_of_two_active_calls
end AspisR1S9ForwardLoopConstructorV1
