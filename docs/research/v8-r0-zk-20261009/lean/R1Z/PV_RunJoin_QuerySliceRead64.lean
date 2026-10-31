import R1Z.PV_RunJoin_QueryReadBounds64
set_option autoImplicit false
namespace R1Z.PV_RunJoin_QuerySliceRead64
open Aeneas Aeneas.Std Result

theorem bound {T : Type} (s : Slice T) (i : Usize) (x : T) (success : Slice.index_usize s i=ok x) :
    i.val<s.length := by
  by_contra denied
  change (match s.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some y => Result.ok y)=ok x at success
  have hnone : s.val[i.val]?=none := by
    exact List.getElem?_eq_none (Nat.le_of_not_gt denied)
  rw [hnone] at success
  cases success

theorem value {T : Type} (s : Slice T) (i : Usize) (x : T) (success : Slice.index_usize s i=ok x) :
    ∃ h : i.val<s.length, s.val[i.val]'h=x := by
  have h := bound s i x success
  change (match s.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some y => Result.ok y)=ok x at success
  rw [List.getElem?_eq_getElem h] at success
  exact ⟨h,Result.ok.inj success⟩

#print axioms bound
#print axioms value
end R1Z.PV_RunJoin_QuerySliceRead64
