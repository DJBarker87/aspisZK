import R1Z.PV_RunJoin_SamplerPass54
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerPrefix54
open PV_RunJoin_CircleNeutralShape53

def Prefix (n : Nat) (a : Array U32 4#usize) : Prop :=
  ∀ j : Fin 4, j.val<n → Canon (a.val[j.val]'(by rw [a.property];exact j.isLt))
theorem zero (a : Array U32 4#usize) : Prefix 0 a := by intro j hj;omega

theorem update (a : Array U32 4#usize) (n : Usize) (v : U32) (small : n.val<4)
    (before : Prefix n.val a) (canonical : Canon v) :
    ∃ next,Array.update a n v=ok next ∧ Prefix (n.val+1) next := by
  have bound : n.val<a.val.length := by rw [a.property];exact small
  obtain ⟨next,hr,hset⟩ := WP.spec_imp_exists (Array.update_spec a n v bound)
  refine ⟨next,hr,?_⟩
  intro j hj
  simp only [hset,Aeneas.Std.Array.set,List.getElem_set]
  by_cases same : n.val=j.val
  · simp only [same,if_true]
    exact canonical
  · simp only [same,if_false]
    apply before j
    omega
#print axioms Prefix
#print axioms zero
#print axioms update
end R1Z.PV_RunJoin_SamplerPrefix54
