import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_VectorPopSpec
set_option autoImplicit false

/-- Pure complete-result specification. The unsupported extracted source
binding and timed-out native checks remain separate, open obligations. -/
def pop {T : Type} (v : alloc.vec.Vec T) : Option T×alloc.vec.Vec T :=
  (v.val.getLast?,⟨v.val.dropLast,by
    rw [List.length_dropLast]
    exact le_trans (Nat.sub_le _ _) v.property⟩)

def reference {T : Type} (v : alloc.vec.Vec T) : Result (Option T×alloc.vec.Vec T) :=
  ok (pop v)

theorem length {T : Type} (v : alloc.vec.Vec T) : (pop v).2.val.length=v.val.length-1 := by
  simp only [pop,List.length_dropLast]

theorem total {T : Type} (v : alloc.vec.Vec T) : ∃ p, reference v=ok p := ⟨pop v,rfl⟩
#print axioms pop
#print axioms reference
#print axioms length
#print axioms total
end R1Z.PV_CBL_VectorPopSpec
