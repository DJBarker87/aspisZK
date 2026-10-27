import R1Z.PV_CBL_ArrayQM31
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayResult
set_option autoImplicit false
abbrev Q := PV_CBL_ArrayQM31.Q

/-- Complete Result adapter; source binding is a separate required gate. -/
def reference (v : alloc.vec.Vec Q) :
    Result (core.result.Result (Array Q 1024#usize) (alloc.vec.Vec Q)) := do
  let a ← PV_CBL_ArrayQM31.reference (alloc.vec.Vec.deref v)
  match a with
  | some a => ok (.Ok a)
  | none => ok (.Err v)

theorem reject (v : alloc.vec.Vec Q) (h : alloc.vec.Vec.len v≠1024#usize) :
    reference v=ok (.Err v) := by
  unfold reference
  have hr := PV_CBL_ArrayQM31.reject (alloc.vec.Vec.deref v) h
  simp only [hr,bind_tc_ok]

theorem success (v : alloc.vec.Vec Q) (h : alloc.vec.Vec.len v=1024#usize) :
    ∃ a, reference v=ok (.Ok a) ∧ a.val=v.val := by
  obtain ⟨a,ha,hav⟩ := PV_CBL_ArrayQM31.success (alloc.vec.Vec.deref v) h
  exact ⟨a,by simp only [reference,ha,bind_tc_ok],hav⟩
#print axioms reference
#print axioms reject
#print axioms success
end R1Z.PV_CBL_ArrayResult
