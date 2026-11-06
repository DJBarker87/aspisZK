import CheckpointBytes4Comparison
set_option autoImplicit false
namespace NKK_Compare
open Aeneas Aeneas.Std Result AspisR1

theorem list_result (xs ys : List U8) :
 CheckpointBytes4Ops.listEq core.cmp.PartialEqU8 xs ys=ok (decide (xs=ys)) := by
 induction xs generalizing ys with
 | nil => cases ys <;> rfl
 | cons x xs ih =>
  cases ys with
  | nil => rfl
  | cons y ys =>
   change (if decide (x=y) then CheckpointBytes4Ops.listEq core.cmp.PartialEqU8 xs ys else ok false)=_
   by_cases h : x=y
   · subst y
     simpa only [List.cons.injEq,true_and,decide_true,if_true] using ih ys
   · have different : x::xs≠y::ys := fun same=>h (List.cons.inj same).1
     simp only [h,different,decide_false]
     rfl

theorem eq_result {n : Usize} (s : Slice U8) (a : Array U8 n) :
 CheckpointBytes4Ops.eq core.cmp.PartialEqU8 s a=ok (decide (s.val=a.val)) := by
 unfold CheckpointBytes4Ops.eq
 split
 · exact list_result s.val a.val
 · have different : s.val≠a.val := by intro same;rename_i h;exact h (congrArg List.length same)
   simp only [different,decide_false]

theorem ne_result {n : Usize} (s : Slice U8) (a : Array U8 n) :
 CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s a=ok (decide (s.val≠a.val)) := by
 unfold CheckpointBytes4Ops.ne
 rw [eq_result]
 by_cases same : s.val=a.val <;> simp [same]

/-- Exact returning and rejecting comparison. No successful-hash premise. -/
theorem branch {n : Usize} (s : Slice U8) (a : Array U8 n) :
 (do let different ← CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s a
     if different then ok (core.result.Result.Err AspisR1Stage2.verifier.Error.Checkpoint)
     else ok (core.result.Result.Ok ()))=
 ok (if s.val=a.val then core.result.Result.Ok () else .Err .Checkpoint) := by
 rw [ne_result]
 by_cases same : s.val=a.val <;> simp [same]

#print axioms list_result
#print axioms eq_result
#print axioms ne_result
#print axioms branch
end NKK_Compare
