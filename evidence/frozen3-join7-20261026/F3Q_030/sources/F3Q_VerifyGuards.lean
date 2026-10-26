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
  all_goals simp_all
  all_goals
    change ok (⟨nodes.len.bv.umod (32#usize).bv⟩ : Usize)=ok 0#usize
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    change (nodes.len.bv % (32#usize).bv).toNat=0
    have literal : (32#usize).bv = 32#System.Platform.numBits := by rfl
    rw [literal]
    assumption

#print axioms accepted
end AspisR1.F3Q_VerifyGuards
end
