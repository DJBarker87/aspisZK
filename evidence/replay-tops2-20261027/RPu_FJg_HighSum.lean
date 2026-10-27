import RPu_FJg_HighValue
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_HighSum
open Aeneas Aeneas.Std
open FIo_FieldBridge (NQ NE)
open scoped BigOperators

theorem sumPrefix (p : Array NE 4#usize) (q : Array NQ 4#usize) (n : Nat) :
    FJg_HighCell.sumPrefix p q n=∑ j∈Finset.range n,FJg_HighCell.term p q j := by
  induction n with
  | zero => simp only [FJg_HighCell.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [FJg_HighCell.sumPrefix,Finset.sum_range_succ,ih]

theorem four (p : Array NE 4#usize) (q : Array NQ 4#usize) :
    FJg_HighCell.sumPrefix p q 4=∑ j : Fin 4,FIp_ArrayValue.value p j.val*
      algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJf_QMArray.value q j.val) := by
  have sums : FJg_HighCell.sumPrefix p q 4=∑ j : Fin 4,FJg_HighCell.term p q j.val := by
    rw [sumPrefix,Fin.sum_univ_eq_sum_range]
  rw [sums]
  rfl
#print axioms sumPrefix
#print axioms four
end AspisR1.FJg_HighSum
end
