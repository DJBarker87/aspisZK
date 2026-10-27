import RPu_FIy_OccupancyLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_OccupancyClosed
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)

theorem value (a : Array NQ 16#usize) (m b : NQ) (n lane : Nat)
    (old : Fin (12#usize).val → K) (j : Fin (12#usize).val) :
    FIy_OccupancyLoop.model a m b n lane old j=
      if 3+lane≤j.val ∧ j.val<3+lane+n then
        decode b*(decode m*FIv_NativeArray.value a (j.val-1)) else old j := by
  induction n generalizing lane old with
  | zero=>
    simp only [FIy_OccupancyLoop.model,Nat.add_zero,
      if_neg (show ¬(3+lane≤j.val ∧ j.val<3+lane) by omega)]
  | succ n ih=>
    rw [FIy_OccupancyLoop.model,ih]
    unfold FIy_OccupancyStep.model
    by_cases he : j.val=3+lane
    · have difference : j.val-1=2+lane := by omega
      rw [if_neg (show ¬(3+(lane+1)≤j.val ∧ j.val<3+(lane+1)+n) by omega),
        if_pos he,if_pos (show 3+lane≤j.val ∧ j.val<3+lane+(n+1) by omega),difference]
    · rw [if_neg he]
      by_cases inside : 3+lane≤j.val ∧ j.val<3+lane+(n+1)
      · rw [if_pos inside,if_pos (by omega)]
      · rw [if_neg inside,if_neg (by omega)]
#print axioms value
end AspisR1.FIy_OccupancyClosed
end
