import Port4B_VerifyInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_VerifyGuards
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem accepted (run : reference.Scratch → Result reference.Level)
    (root : Array U8 32#usize) (s out : reference.Scratch) (nodes : Slice U8)
    (success : MultiproofConeP6Verify.wrapper run root s nodes=ok (true,out)) :
    s.n≠0#usize ∧ ¬s.n>16#usize ∧
    reference.valid_indices s.idx s.n 0#usize=ok true ∧
    Slice.len nodes % 32#usize=ok 0#usize := by
  unfold MultiproofConeP6Verify.wrapper at success
  repeat' first
  | (solve | cases success)
  | uncase_result
  | head_reduce success
  | split at success
  all_goals
    refine ⟨by assumption,by assumption,by assumption,?_⟩
    rename_i rem remCall remZero
    have zero : rem=0#usize := by simpa only [Bool.not_eq_true,decide_eq_false_iff_not,ne_eq,not_not] using remZero
    simpa only [zero] using remCall

#print axioms accepted
end AspisR1.F3Q_VerifyGuards
end
