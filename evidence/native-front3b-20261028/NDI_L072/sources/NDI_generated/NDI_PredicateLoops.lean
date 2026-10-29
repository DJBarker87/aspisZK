import NDI_PredicatesBridge
import Port5Q2_ReaderValidate
set_option autoImplicit false
namespace NDI_PredicateLoops
open Aeneas Aeneas.Std Result

theorem pure_any {α : Type} (p : α → Bool) (xs : List α) :
    List.anyM (fun x => ok (p x)) xs=ok (xs.any p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.anyM,bind_tc_ok,List.any_cons,ih]
    cases p x <;> rfl

theorem tail (xs : List U8) :
    List.anyM NDI_PredicatesRef.tail_predicate_ref xs=ok (xs.any (fun x=>x != 0#u8)) :=
  pure_any (fun x=>x != 0#u8) xs

theorem contains (xs : List U32) (q : U32) :
    List.anyM (fun x=>NDI_PredicatesRef.contains_predicate_ref x q) xs=ok (decide (q∈xs)) := by
  change List.anyM (fun x=>ok (decide (x=q))) xs=ok (decide (q∈xs))
  rw [pure_any]
  apply congrArg Result.ok
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true,eq_comm]

theorem emitted_contains (s : Slice U32) (q : U32) :
    List.anyM (fun x=>NDI_PredicatesRef.contains_predicate_ref x q) s.val=
      core.slice.Slice.contains core.cmp.PartialEqU32 s q := by
  rw [contains,AspisR1.Port5Q2_ReaderValidate.contains]

#print axioms pure_any
#print axioms tail
#print axioms contains
#print axioms emitted_contains
end NDI_PredicateLoops
