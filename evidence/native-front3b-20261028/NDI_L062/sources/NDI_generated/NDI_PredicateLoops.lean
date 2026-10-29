import NDI_PredicatesBridge
import Port5Q2_ReaderValidate
set_option autoImplicit false
namespace NDI_PredicateLoops
open Aeneas Aeneas.Std Result

theorem tail (xs : List U8) :
    List.anyM NDI_PredicatesRef.tail_predicate_ref xs=ok (xs.any (fun x=>x!=0#u8)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases nonzero : x=0#u8 <;>
      simp [List.anyM,NDI_PredicatesRef.tail_predicate_ref,List.any_cons,nonzero,ih]

theorem contains (xs : List U32) (q : U32) :
    List.anyM (fun x=>NDI_PredicatesRef.contains_predicate_ref x q) xs=ok (decide (q∈xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases same : x=q <;>
      simp [List.anyM,NDI_PredicatesRef.contains_predicate_ref,List.mem_cons,same,ih,eq_comm]

theorem emitted_contains (s : Slice U32) (q : U32) :
    List.anyM (fun x=>NDI_PredicatesRef.contains_predicate_ref x q) s.val=
      core.slice.Slice.contains core.cmp.PartialEqU32 s q := by
  rw [contains,AspisR1.Port5Q2_ReaderValidate.contains]

#print axioms tail
#print axioms contains
#print axioms emitted_contains
end NDI_PredicateLoops
