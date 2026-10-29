import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FromElemLength60
open Aeneas Aeneas.Std Result PV_RunJoin_ResultPost41

theorem complete {A : Type} (clone : core.clone.Clone A) (x : A) (n : Usize)
    (out : alloc.vec.Vec A) (success : alloc.vec.from_elem clone x n=ok out) :
    out.length=n.val := by
  unfold alloc.vec.from_elem at success
  obtain ⟨l,_,he⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
  cases he
  change l.val.length=n.val
  simpa only [List.length_replicate] using l.property

#print axioms complete
end R1Z.PV_RunJoin_FromElemLength60
