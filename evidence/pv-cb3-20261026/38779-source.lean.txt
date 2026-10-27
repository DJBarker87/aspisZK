import R1Z.PV_CB3_Op258Frame
import R1Z.PV_CB3_Op258Total
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258False
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull

theorem loop_false
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (bound : values.val.length ≤ 1024)
    (row : Usize) (hrow : row.val ≤ values.val.length) :
    PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi false row = ok false := by
  have aux : ∀ fuel : Nat, ∀ row : Usize, row.val ≤ values.val.length →
      values.val.length-row.val < fuel →
      PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi false row = ok false := by
    intro fuel
    induction fuel with
    | zero => intro row hrow hfuel; omega
    | succ fuel ih =>
      intro row hrow hfuel
      by_cases hr : row < Slice.len values
      · have hn : row.val < values.val.length := by
          change row.val < (Slice.len values).val at hr
          simpa only [PV_CB3_PoleIndex.slice_length] using hr
        have hs : row.val < 1024 := by omega
        have hstep := PV_CB3_Op258Frame.false_step values masks chi row hr hs
        have hi := PV_CB3_PoleIndex.increment row hs
        have ht := ih (Usize.wrapping_add row 1#usize) (by omega) (by omega)
        calc
          _ = PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi false
              (Usize.wrapping_add row 1#usize) :=
            PV_CB3_LoopEquations.continue_step _ (false,row) _ hstep
          _ = ok false := ht
      · exact PV_CB3_LoopEquations.done_step _ (false,row) _
          (PV_CB3_Op258End.body_done values masks chi false row hr)
  exact aux (values.val.length+1) row hrow (by omega)

theorem loop_frame
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (bound : values.val.length ≤ 1024)
    (row : Usize) (hrow : row.val ≤ values.val.length) :
    ∃ keep, ∀ clear,
      PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi clear row = ok (clear && keep) := by
  obtain ⟨keep,hkeep⟩ := PV_CB3_Op258Total.loop_total values masks chi bound row true hrow
  refine ⟨keep,?_⟩
  intro clear
  cases clear with
  | false => simpa only [Bool.false_and] using loop_false values masks chi bound row hrow
  | true => simpa only [Bool.true_and] using hkeep
#print axioms loop_false
#print axioms loop_frame
end R1Z.PV_CB3_Op258False
