import R1Z.PV_RunJoin_SemanticSourceSuccess51
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PointPrefix51
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitSubfieldOps47
abbrev Q := ProverRwFull.aspis_core.field.QM31

def Prefix (n : Nat) (a : Array Q 10#usize) : Prop :=
  ∀ j : Fin 10,j.val<n → Canonical (PV_RunJoin_SemanticScalar50.raw (a.val[j.val]'(by rw [a.property];exact j.isLt)))

theorem zero (a : Array Q 10#usize) : Prefix 0 a := by
  intro j hj
  omega

theorem update (a : Array Q 10#usize) (n : Usize) (v : Q) (small : n.val<10)
    (before : Prefix n.val a) (canonical : Canonical (PV_RunJoin_SemanticScalar50.raw v)) :
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
end R1Z.PV_RunJoin_PointPrefix51
