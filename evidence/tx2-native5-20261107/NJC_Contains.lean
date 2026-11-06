import NJC_ValidateEmission
set_option autoImplicit false
noncomputable section
namespace NJC_Contains
open Aeneas Aeneas.Std Result

theorem scalar (a b : U32) : core.cmp.PartialEqU32.eq a b=ok (decide (a=b)) := by
 rfl

/-- The emitted std child, on the SAME prefix and needle. This is a library
model law under the retained Std/P6 boundary; no new native/runtime trust. -/
theorem list (xs : List U32) (q : U32) :
 List.anyM (core.cmp.PartialEqU32.eq q) xs=ok (decide (q∈xs)) := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
  simp only [List.anyM,scalar,bind_tc_ok,ih,List.mem_cons]
  by_cases eq : q=x <;> simp [eq]
  all_goals rfl

theorem source (s : Slice U32) (q : U32) :
 core.slice.Slice.contains core.cmp.PartialEqU32 s q=ok (decide (q∈s.val)) :=
 list s.val q
#print axioms scalar
#print axioms list
#print axioms source
end NJC_Contains
