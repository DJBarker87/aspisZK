import RPu_FIx_PathLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PathModel
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)

def left (selector bit : NQ) (a a1 : Array NQ 16#usize) (lane : Nat) : K :=
  decode selector*(1-decode bit)*(FIv_NativeArray.value a1 lane-FIv_NativeArray.value a (1+lane))
def right (selector bit : NQ) (a a1 : Array NQ 16#usize) (lane : Nat) : K :=
  decode selector*decode bit*(FIv_NativeArray.value a1 (8+lane)-FIv_NativeArray.value a (1+lane))

theorem value (selector bit : NQ) (a a1 : Array NQ 16#usize) (n lane : Nat)
    (old : Fin (17#usize).val → K) (j : Fin (17#usize).val) (span : lane+n≤8) :
    FIx_PathLoop.model selector bit a a1 n lane old j=
      if 9+lane≤j.val ∧ j.val<9+(lane+n) then right selector bit a a1 (j.val-9)
      else if 1+lane≤j.val ∧ j.val<1+(lane+n) then left selector bit a a1 (j.val-1)
      else old j := by
  induction n generalizing lane old with
  | zero =>
    simp only [FIx_PathLoop.model,Nat.add_zero,
      if_neg (show ¬(9+lane≤j.val ∧ j.val<9+lane) by omega),
      if_neg (show ¬(1+lane≤j.val ∧ j.val<1+lane) by omega)]
  | succ n ih =>
    rw [FIx_PathLoop.model,ih (lane+1) _ (by omega)]
    unfold FIx_PathAlgebra.step
    by_cases hr : j.val=9+lane
    · have difference : j.val-9=lane := by omega
      rw [if_neg (show ¬(9+(lane+1)≤j.val ∧ j.val<9+(lane+1+n)) by omega),
        if_neg (show ¬(1+(lane+1)≤j.val ∧ j.val<1+(lane+1+n)) by omega),
        if_pos hr,if_pos (show 9+lane≤j.val ∧ j.val<9+(lane+(n+1)) by omega),difference]
      rfl
    · by_cases hl : j.val=1+lane
      · have difference : j.val-1=lane := by omega
        rw [if_neg (show ¬(9+(lane+1)≤j.val ∧ j.val<9+(lane+1+n)) by omega),
          if_neg (show ¬(1+(lane+1)≤j.val ∧ j.val<1+(lane+1+n)) by omega),
          if_neg hr,if_pos hl,
          if_neg (show ¬(9+lane≤j.val ∧ j.val<9+(lane+(n+1))) by omega),
          if_pos (show 1+lane≤j.val ∧ j.val<1+(lane+(n+1)) by omega),difference]
        rfl
      · rw [if_neg hr,if_neg hl]
        have eqr : (9+(lane+1)≤j.val ∧ j.val<9+(lane+1+n)) ↔
            (9+lane≤j.val ∧ j.val<9+(lane+(n+1))) := by omega
        have eql : (1+(lane+1)≤j.val ∧ j.val<1+(lane+1+n)) ↔
            (1+lane≤j.val ∧ j.val<1+(lane+(n+1))) := by omega
        simp only [eqr,eql]
#print axioms value
end AspisR1.FIx_PathModel
end
