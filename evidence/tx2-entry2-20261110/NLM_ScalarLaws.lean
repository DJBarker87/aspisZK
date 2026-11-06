import NLM_ReadCalls
set_option autoImplicit false
namespace NLM_ScalarLaws
open Aeneas Aeneas.Std
/-- Keep scalar equality symbolic; never normalize a generated recurrence. -/
theorem scalar_eq {ty : UScalarTy} (a b : UScalar ty) (same : a.val=b.val) : a=b := by
 cases a with
 | mk x =>
   cases b with
   | mk y =>
     congr 1
     exact BitVec.eq_of_toNat_eq same

theorem length_eq (bytes : Slice U8) (n : Usize) :
 Slice.len bytes=n ↔ bytes.val.length=n.val := by
 constructor
 · intro same
   have h := congrArg (fun x : Usize => x.val) same
   simpa only [Slice.len_val] using h
 · intro same
   apply scalar_eq
   simpa only [Slice.len_val] using same
#print scalar_eq
#print length_eq
#print axioms scalar_eq
#print axioms length_eq
end NLM_ScalarLaws
