import Aeneas
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometryCaller
open Aeneas Aeneas.Std Result

/-- Successful source query calls advance the counter by exactly one. This
reachability certificate is used by the enclosing source-loop induction;
it does not assume that arbitrary external counter states are reachable. -/
inductive Calls (start : Usize) : Usize → Prop where
  | initial : Calls start start
  | advance {index next : Usize} : Calls start index →
      next.val = index.val + 1 → Calls start next

theorem lower_bound {start index : Usize} (h : Calls start index) :
    start.val ≤ index.val := by
  induction h with
  | initial => omega
  | advance _ hnext ih => omega

/-- The upper bound is the actual while-guard branch at the call site. -/
theorem call_range {start finish index : Usize}
    (h : Calls start index) (guard : index < finish) :
    start.val ≤ index.val ∧ index.val < finish.val := by
  exact ⟨lower_bound h,guard⟩

theorem offset_bound {start finish index : Usize}
    (h : Calls start index) (guard : index < finish) :
    index.val-start.val < finish.val-start.val := by
  have := call_range h guard
  omega

/-- One public single-query invocation builds precisely [next,next+1). -/
theorem single_range (index : Usize) (hindex : index.val < 22) :
    ∃ finish : Usize,(index+1#usize : Result Usize)=.ok finish ∧
      index.val ≤ index.val ∧ index.val < finish.val ∧ finish.val ≤ 22 := by
  have hone : (1#usize).val=1 := by scalar_tac
  have hlarge : 22 ≤ UScalar.max .Usize := by scalar_tac
  have hsum : index.val+(1#usize).val ≤ UScalar.max .Usize := by omega
  obtain ⟨finish,hs,hval⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=index) (y:=1#usize) hsum)
  exact ⟨finish,hs,by omega,by omega,by omega⟩

#print axioms lower_bound
#print axioms call_range
#print axioms offset_bound
#print axioms single_range
end AspisR1.CuSavingsGeometryCaller
