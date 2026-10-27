import FIx_ValueBitModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ValueBitClosed
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)

theorem value (a : Array NQ 16#usize) (offset n index : Nat)
    (old : Fin (33#usize).val → K) (j : Fin (33#usize).val) :
    FIx_ValueBitModel.model a offset n index old j=
      if offset+index≤j.val ∧ j.val<offset+index+n then
        FIx_ValueBitModel.bit a (j.val-offset) else old j := by
  induction n generalizing index old with
  | zero =>
    simp only [FIx_ValueBitModel.model,Nat.add_zero,
      if_neg (show ¬(offset+index≤j.val ∧ j.val<offset+index) by omega)]
  | succ n ih =>
    rw [FIx_ValueBitModel.model,ih]
    unfold FIx_ValueBitModel.step
    by_cases he : j.val=offset+index
    · have difference : j.val-offset=index := by omega
      rw [if_neg (show ¬(offset+(index+1)≤j.val ∧ j.val<offset+(index+1)+n) by omega),
        if_pos he,if_pos (show offset+index≤j.val ∧ j.val<offset+index+(n+1) by omega),difference]
    · rw [if_neg he]
      have h : (offset+(index+1)≤j.val ∧ j.val<offset+(index+1)+n) ↔
          (offset+index≤j.val ∧ j.val<offset+index+(n+1)) := by omega
      by_cases inside : offset+index≤j.val ∧ j.val<offset+index+(n+1)
      · rw [if_pos inside,if_pos (h.mpr inside)]
      · rw [if_neg inside,if_neg (fun x=>inside (h.mp x))]
#print axioms value
end AspisR1.FIx_ValueBitClosed
end
