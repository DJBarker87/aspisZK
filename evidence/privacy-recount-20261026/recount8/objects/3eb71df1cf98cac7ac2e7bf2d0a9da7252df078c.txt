import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_ArrayOwnership
set_option autoImplicit false

/-- Ownership-level specification, polymorphic without a Copy/Clone input.
This is a specification, not an extracted replacement for native ptr::read,
allocator deallocation, or destructor semantics. -/
def value {T : Type} (N : Usize) (v : alloc.vec.Vec T) :
    core.result.Result (Array T N) (alloc.vec.Vec T) :=
  if h : v.val.length=N.val then .Ok ⟨v.val,h⟩ else .Err v

theorem rejection {T : Type} (N : Usize) (v : alloc.vec.Vec T)
    (h : v.val.length≠N.val) : value N v=.Err v := by
  simp only [value,dif_neg h]

theorem success {T : Type} (N : Usize) (v : alloc.vec.Vec T)
    (h : v.val.length=N.val) :
    ∃ a, value N v=.Ok a ∧ a.val=v.val := by
  exact ⟨⟨v.val,h⟩,by simp only [value,dif_pos h],rfl⟩

theorem complete {T : Type} (N : Usize) (v : alloc.vec.Vec T) :
    (value N v=.Err v ∧ v.val.length≠N.val) ∨
      (∃ a, value N v=.Ok a ∧ a.val=v.val ∧ v.val.length=N.val) := by
  by_cases h : v.val.length=N.val
  · obtain ⟨a,ha,hv⟩ := success N v h
    exact Or.inr ⟨a,ha,hv,h⟩
  · exact Or.inl ⟨rejection N v h,h⟩

#print axioms value
#print axioms rejection
#print axioms success
#print axioms complete
end R1Z.PV_DL_ArrayOwnership
