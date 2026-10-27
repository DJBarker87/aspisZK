import PV_B1_Orig258_Op258Step
import PV_B1_Orig258_Op258Failure
set_option autoImplicit false
noncomputable section
namespace PV_B1_Orig258_Op258Outside
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258

/-- Oversized slices fail even if the Boolean accumulator became false earlier. -/
theorem loop_failure
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (oversized : 1024 < values.val.length)
    (row : Usize) (clear : Bool) (hrow : row.val ≤ 1024) :
    PV_B1_PoleOriginal.reference.all_slots_clear_loop values masks chi clear row = fail .arrayOutOfBounds := by
  have aux : ∀ fuel : Nat, ∀ (row : Usize) (clear : Bool),
      row.val ≤ 1024 → 1025-row.val < fuel →
      PV_B1_PoleOriginal.reference.all_slots_clear_loop values masks chi clear row = fail .arrayOutOfBounds := by
    intro fuel
    induction fuel with
    | zero => intro row clear hrow hfuel; omega
    | succ fuel ih =>
      intro row clear hrow hfuel
      have hr : row < Slice.len values := by
        change row.val < (Slice.len values).val
        rw [PV_B1_Orig258_PoleIndex.slice_length]
        omega
      by_cases hs : row.val < 1024
      · obtain ⟨next,hstep⟩ := PV_B1_Orig258_Op258Step.total values masks chi clear row hr hs
        have hi := PV_B1_Orig258_PoleIndex.increment row hs
        have ht := ih (Usize.wrapping_add row 1#usize) next (by omega) (by omega)
        calc
          _ = PV_B1_PoleOriginal.reference.all_slots_clear_loop values masks chi next
              (Usize.wrapping_add row 1#usize) :=
            PV_B1_LoopSteps.continue_step _ (clear,row) _ hstep
          _ = fail .arrayOutOfBounds := ht
      · exact PV_B1_Orig258_Op258Failure.loop values masks chi clear row hr (by omega)
  exact aux 1026 row clear hrow (by omega)

theorem source_failure
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (oversized : 1024 < values.val.length) :
    PV_B1_PoleOriginal.reference.all_slots_clear values masks chi = fail .arrayOutOfBounds :=
  loop_failure values masks chi oversized 0#usize true (by change 0 ≤ 1024; omega)
#print axioms loop_failure
#print axioms source_failure
end PV_B1_Orig258_Op258Outside
