import RPv_FIy_DigestLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_DigestClosed
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)

theorem value (selector : NQ) (opened : Array NQ 16#usize) (start : Nat)
    (expected : Array U32 8#usize) (right : Bool) (n lane : Nat)
    (old : Fin (8#usize).val → K) (j : Fin (8#usize).val) :
    FIy_DigestLoop.model selector opened start expected right n lane old j=
      if lane≤j.val ∧ j.val<lane+n then
        old j+FIy_DigestLane.increment selector opened start expected right j.val else old j := by
  induction n generalizing lane old with
  | zero=>
    simp only [FIy_DigestLoop.model,Nat.add_zero,if_neg (show ¬(lane≤j.val ∧ j.val<lane) by omega)]
  | succ n ih=>
    rw [FIy_DigestLoop.model,ih]
    unfold FIy_DigestLane.model
    by_cases he : j.val=lane
    · rw [if_neg (show ¬(lane+1≤j.val ∧ j.val<lane+1+n) by omega),
        if_pos he,if_pos (show lane≤j.val ∧ j.val<lane+(n+1) by omega)]
    · rw [if_neg he]
      by_cases inside : lane≤j.val ∧ j.val<lane+(n+1)
      · rw [if_pos inside,if_pos (by omega)]
      · rw [if_neg inside,if_neg (by omega)]
#print axioms value
end AspisR1.FIy_DigestClosed
end
