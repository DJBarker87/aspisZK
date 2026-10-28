import R1Z.PV_RunJoin_FoldCell44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceUpdate44
open Aeneas Aeneas.Std Result
open ProverCommitWideOps48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)

theorem update (size : Usize) (xs : Nat → Raw) (i : Usize) (hi : i.val < size.val) (z : Raw) :
    Array.update (array size xs) i (current (source z)) = .ok (array size (Function.update xs i.val z)) := by
  unfold array
  rw [ProverCommitArray49.update size (fun k => current (source (xs k))) i hi (current (source z))]
  apply congrArg Result.ok
  apply congrArg (ProverCommitArray49.array size)
  funext k
  by_cases h : k = i.val
  · subst k;simp only [Function.update_self]
  · simp only [Function.update_of_ne h]
#print axioms update
end R1Z.PV_RunJoin_SourceUpdate44
