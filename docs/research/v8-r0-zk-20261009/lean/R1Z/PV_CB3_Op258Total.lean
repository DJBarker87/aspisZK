import R1Z.PV_CB3_Op258Step
import R1Z.PV_CB3_LoopEquations
import R1Z.PV_CB3_Op258End
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258Total
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull

theorem loop_total
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (bound : values.val.length ≤ 1024)
    (row : Usize) (clear : Bool) (hrow : row.val ≤ values.val.length) :
    ∃ out, PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi clear row = ok out := by
  have aux : ∀ fuel : Nat, ∀ (row : Usize) (clear : Bool),
      row.val ≤ values.val.length → values.val.length-row.val < fuel →
      ∃ out, PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi clear row = ok out := by
    intro fuel
    induction fuel with
    | zero => intro row clear hrow hfuel; omega
    | succ fuel ih =>
      intro row clear hrow hfuel
      by_cases hr : row < Slice.len values
      · have hn : row.val < values.val.length := by
          change row.val < (Slice.len values).val at hr
          simpa only [PV_CB3_PoleIndex.slice_length] using hr
        have hs : row.val < 1024 := by omega
        obtain ⟨next,hnative⟩ := PV_CB3_Op258Step.total values masks chi clear row hr hs
        have hi := PV_CB3_PoleIndex.increment row hs
        obtain ⟨out,hout⟩ := ih (Usize.wrapping_add row 1#usize) next (by omega) (by omega)
        refine ⟨out,?_⟩
        calc
          _ = PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi next
              (Usize.wrapping_add row 1#usize) :=
            PV_CB3_LoopEquations.continue_step _ (clear,row) _ hnative
          _ = ok out := hout
      · exact ⟨clear,PV_CB3_LoopEquations.done_step _ (clear,row) _
          (PV_CB3_Op258End.body_done values masks chi clear row hr)⟩
  exact aux (values.val.length+1) row clear hrow (by omega)

theorem source_total
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (bound : values.val.length ≤ 1024) :
    ∃ out, PV_CB3_Op258Ref.reference.all_slots_clear values masks chi = ok out :=
  loop_total values masks chi bound 0#usize true (by change 0 ≤ _; omega)
#print axioms loop_total
#print axioms source_total
end R1Z.PV_CB3_Op258Total
