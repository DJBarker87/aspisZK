import R1Z.PV_RunJoin_ListUpdatePrefix50
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ArrayUpdatePrefix50
open Aeneas Aeneas.Std Result

theorem complete {A : Type} {n : Usize} (a : Array A n) (i : Usize) (v : A) (hi : i.val<n.val) :
    ∃ next, Array.update a i v=ok next ∧
      next.val.take (i.val+1)=a.val.take i.val ++ [v] := by
  have bound : i.val<a.val.length := by rw [a.property];exact hi
  obtain ⟨next,hr,hset⟩ := WP.spec_imp_exists (Array.update_spec a i v bound)
  refine ⟨next,hr,?_⟩
  rw [hset]
  exact PV_RunJoin_ListUpdatePrefix50.complete a.val i.val v bound
#print axioms complete
end R1Z.PV_RunJoin_ArrayUpdatePrefix50
