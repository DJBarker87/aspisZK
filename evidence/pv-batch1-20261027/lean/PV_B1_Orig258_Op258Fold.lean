import PV_B1_Orig258_Op258Frame
import PV_B1_Orig258_Op258Total
set_option autoImplicit false
noncomputable section
namespace PV_B1_Orig258_Op258Fold
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258
abbrev Rows := Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize)

def keep (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (row : Usize) : Bool :=
  match PV_B1_PoleOriginal.reference.all_slots_clear_loop.body values masks chi true row with
  | ok (cont (b,_)) => b
  | _ => false

def scan (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) : Nat → Usize → Bool
  | 0, _ => true
  | n+1, row => keep values masks chi row && scan values masks chi n (Usize.wrapping_add row 1#usize)

theorem body_frame (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (row : Usize) (hr : row < Slice.len values) (hm : row.val < 1024) (clear : Bool) :
    PV_B1_PoleOriginal.reference.all_slots_clear_loop.body values masks chi clear row =
      ok (cont (clear && keep values masks chi row,Usize.wrapping_add row 1#usize)) := by
  obtain ⟨b,hb⟩ := PV_B1_Orig258_Op258Frame.step_frame values masks chi row hr hm
  have ht := hb true
  simp only [Bool.true_and] at ht
  have hk : keep values masks chi row = b := by simp only [keep,ht]
  rw [hk]
  exact hb clear

theorem loop_scan (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (bound : values.val.length ≤ 1024) (n : Nat) (row : Usize) (clear : Bool)
    (hlen : row.val+n = values.val.length) :
    PV_B1_PoleOriginal.reference.all_slots_clear_loop values masks chi clear row =
      ok (clear && scan values masks chi n row) := by
  induction n generalizing row clear with
  | zero =>
    have hr : ¬ row < Slice.len values := by
      change ¬ row.val < (Slice.len values).val
      rw [PV_B1_Orig258_PoleIndex.slice_length]
      omega
    have hd : PV_B1_PoleOriginal.reference.all_slots_clear_loop values masks chi clear row = ok clear :=
      PV_B1_LoopSteps.done_step _ (clear,row) _
        (PV_B1_Orig258_Op258End.body_done values masks chi clear row hr)
    simpa only [scan,Bool.and_true] using hd
  | succ n ih =>
    have hr : row < Slice.len values := by
      change row.val < (Slice.len values).val
      rw [PV_B1_Orig258_PoleIndex.slice_length]
      omega
    have hm : row.val < 1024 := by omega
    have hi := PV_B1_Orig258_PoleIndex.increment row hm
    have hstep := body_frame values masks chi row hr hm clear
    calc
      _ = PV_B1_PoleOriginal.reference.all_slots_clear_loop values masks chi
          (clear && keep values masks chi row) (Usize.wrapping_add row 1#usize) :=
        PV_B1_LoopSteps.continue_step _ (clear,row) _ hstep
      _ = ok ((clear && keep values masks chi row) &&
          scan values masks chi n (Usize.wrapping_add row 1#usize)) := ih _ _ (by omega)
      _ = _ := by simp only [scan,Bool.and_assoc]

theorem source_scan (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (bound : values.val.length ≤ 1024) :
    PV_B1_PoleOriginal.reference.all_slots_clear values masks chi =
      ok (scan values masks chi values.val.length 0#usize) := by
  simpa only [Bool.true_and] using loop_scan values masks chi bound values.val.length 0#usize true
    (by change 0+values.val.length=values.val.length; omega)
#print axioms body_frame
#print axioms loop_scan
#print axioms source_scan
end PV_B1_Orig258_Op258Fold
