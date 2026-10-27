import R1Z.PV_CB3_Op258ZeroMaskStep
import R1Z.PV_CB3_Op258Outside
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258ZeroMasks
open Aeneas Aeneas.Std Result ProverRwFull
open PV_CB3_Op258ZeroMaskStep

theorem loop (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (hz : IsZero masks) (bound : values.val.length ≤ 1024)
    (row : Usize) (clear : Bool) (hrow : row.val ≤ values.val.length) :
    PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi clear row = ok clear := by
  have aux : ∀ fuel : Nat, ∀ row : Usize, row.val ≤ values.val.length →
      values.val.length-row.val < fuel →
      PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi clear row = ok clear := by
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
        have hi := PV_CB3_PoleIndex.increment row hs
        have ht := ih (Usize.wrapping_add row 1#usize) (by omega) (by omega)
        calc
          _ = PV_CB3_Op258Ref.reference.all_slots_clear_loop values masks chi clear
              (Usize.wrapping_add row 1#usize) :=
            PV_CB3_LoopEquations.continue_step _ (clear,row) _ (body values masks chi hz clear row hr hs)
          _ = ok clear := ht
      · exact PV_CB3_LoopEquations.done_step _ (clear,row) _
          (PV_CB3_Op258End.body_done values masks chi clear row hr)
  exact aux (values.val.length+1) row hrow (by omega)

/-- Sparse zero-mask case, including the mandatory oversized-slice failure. -/
theorem source (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (hz : IsZero masks) :
    PV_CB3_Op258Ref.reference.all_slots_clear values masks chi =
      if values.val.length ≤ 1024 then ok true else fail .arrayOutOfBounds := by
  split_ifs with h
  · exact loop values masks chi hz h 0#usize true (by change 0≤_; omega)
  · exact PV_CB3_Op258Outside.source_failure values masks chi (by omega)
#print axioms loop
#print axioms source
end R1Z.PV_CB3_Op258ZeroMasks
