import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendInitialLength58
open Aeneas Aeneas.Std Result

theorem complete {T : Type} (clone : core.clone.Clone T) (value : T) (size : Usize)
    (out : alloc.vec.Vec T) (success : alloc.vec.from_elem clone value size=ok out) :
    out.length=size.val := by
  unfold alloc.vec.from_elem at success
  obtain ⟨values,hvalues,hout⟩ := R1Z.PV_RunJoin_ResultPost.bind_eq_ok success
  cases hout
  simpa only [List.length_replicate] using values.property

#print axioms complete
end R1Z.PV_RunJoin_BackendInitialLength58
