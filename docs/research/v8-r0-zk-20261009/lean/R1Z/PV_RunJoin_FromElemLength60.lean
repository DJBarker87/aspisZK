import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FromElemLength60
open Aeneas Aeneas.Std Result PV_RunJoin_ResultPost41

theorem complete {A : Type} (clone : core.clone.Clone A) (x : A) (n : Usize)
    (out : alloc.vec.Vec A) (success : alloc.vec.from_elem clone x n=ok out) :
    out.length=n.val := by
  unfold alloc.vec.from_elem at success
  split at success
  · cases success
  · cases success
    simp only [alloc.vec.Vec.length,List.length_replicate]

#print axioms complete
end R1Z.PV_RunJoin_FromElemLength60
