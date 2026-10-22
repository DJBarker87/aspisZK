import ScheduleEnclosingSlice
import ScheduleProgram

/-! Bind the whole actual generated initial/absorption declaration to the
source-order program whose component premises are already discharged. -/
set_option autoImplicit false
namespace AspisR1.ScheduleEnclosingBridge
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ScheduleProgram

abbrev source := AspisR1ScheduleEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption

theorem enclosing_eq_program (public1 : Public) (openings : Openings) (selectors : Selectors) :
    source public1 openings selectors = AspisR1.ScheduleProgram.run public1 openings selectors := by
  have uncurry_as_projections {α β γ : Type} (f : α → β → γ) :
      Aeneas.Std.uncurry f = fun p : α × β => f p.1 p.2 := by
    funext p
    rcases p with ⟨a, b⟩
    exact Aeneas.Std.uncurry_apply_pair f a b
  unfold source
    AspisR1ScheduleEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption
    AspisR1.ScheduleProgram.run AspisR1.InitialSelectorPrefix.run AspisR1.InitialArrayExecution.run
    AspisR1.ScheduleDomainArithmetic.run AspisR1.InitialArrayWrites.run AspisR1.AbsorptionSelectorSetup.run
    AspisR1.SumHighTwoRanges.pair AspisR1.SumHighTwoRanges.nodeRange1 AspisR1.SumHighTwoRanges.nodeRange2
    AspisR1.ScheduleDomainArithmetic.owner AspisR1.ScheduleDomainArithmetic.note AspisR1.ScheduleDomainArithmetic.nullifier
    AspisR1.InitialArrayWrites.RATE AspisR1.InitialArrayExecution.callbackInst
  simp only [lift, bind_tc_ok, bind_assoc, uncurry_as_projections]

theorem actual_schedule_arrays (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z) :
    ∃ initial absorption,
      source public1 openings selectors = .ok (initial, absorption) ∧
      (∀ i : Fin 16, AspisR1.AbsorptionCallback.Canonical (AspisR1.AbsorptionCallback.sourceCell initial i)) ∧
      (∀ i : Fin 16, AspisR1.AbsorptionCallback.Canonical (AspisR1.AbsorptionCallback.sourceCell absorption i)) ∧
      (∀ i : Fin 16, AspisR1.ExtractedMaskQM31Exact.decode (AspisR1.AbsorptionCallback.sourceCell initial i) =
        R0P.scheduleInitial (modelVariant public1.variant) (exactOpenings openings) (pointSelector point) i) ∧
      ∀ i : Fin 16, AspisR1.ExtractedMaskQM31Exact.decode (AspisR1.AbsorptionCallback.sourceCell absorption i) =
        R0P.scheduleAbsorption (modelVariant public1.variant) (exactOpenings openings) (pointSelector point) i := by
  obtain ⟨initial, absorption, hrun, hci, hca, hvi, hva⟩ :=
    AspisR1.ScheduleProgram.same_boxed_source_success point selectors public1 openings hpoint hbox hz
  exact ⟨initial, absorption, (enclosing_eq_program public1 openings selectors).trans hrun, hci, hca, hvi, hva⟩

#print axioms enclosing_eq_program
#print axioms actual_schedule_arrays
end
end AspisR1.ScheduleEnclosingBridge
