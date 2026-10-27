import OracleProgramReplay
import RPz8_ARW_LocalBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_Cap
open AspisV8R19.MemoizedProgramLaw
/-- An auxiliary bounded observer. It does not alter any admitted execution. -/
def cap {I S O : Type} : Nat → O → Program I S O → Program I S O
  | _, _, .done o => .done o
  | 0, fallback, .ask _ _ => .done fallback
  | n+1, fallback, .ask i k => .ask i (fun s => cap n fallback (k s))
theorem length {I S O : Type} (n : Nat) (fallback : O) (p : Program I S O) (H : I → S) :
    (eval H (cap n fallback p)).1.length ≤ n := by
  induction n generalizing p with
  | zero => cases p <;> exact Nat.zero_le _
  | succ n ih =>
    cases p with
    | done o => exact Nat.zero_le _
    | ask i k => simpa only [cap,eval,List.length_cons] using Nat.succ_le_succ (ih (k (H i)))
theorem exact {I S O : Type} (n : Nat) (fallback : O) (p : Program I S O) (H : I → S)
    (bound : (eval H p).1.length ≤ n) : eval H (cap n fallback p) = eval H p := by
  induction n generalizing p with
  | zero => cases p with
    | done o => rfl
    | ask i k => simp only [eval,List.length_cons] at bound; omega
  | succ n ih =>
    cases p with
    | done o => rfl
    | ask i k =>
      simp only [eval,List.length_cons] at bound
      simp only [cap,eval,ih (k (H i)) (by omega)]
#print axioms length
#print axioms exact
end AspisR1.ARX_Cap
end
