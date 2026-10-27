import R1Z.PV_CBL_ArrayResult
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayResultCases
set_option autoImplicit false

theorem complete (v : alloc.vec.Vec PV_CBL_ArrayQM31.Q) :
    (PV_CBL_ArrayResult.reference v=ok (.Err v) ∧ alloc.vec.Vec.len v≠1024#usize) ∨
    ∃ a, PV_CBL_ArrayResult.reference v=ok (.Ok a) ∧
      alloc.vec.Vec.len v=1024#usize ∧ a.val=v.val := by
  by_cases h : alloc.vec.Vec.len v=1024#usize
  · obtain ⟨a,ha,hav⟩ := PV_CBL_ArrayResult.success v h
    exact Or.inr ⟨a,ha,h,hav⟩
  · exact Or.inl ⟨PV_CBL_ArrayResult.reject v h,h⟩

#print axioms complete
end R1Z.PV_CBL_ArrayResultCases
