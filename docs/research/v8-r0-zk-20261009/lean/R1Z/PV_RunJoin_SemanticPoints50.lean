import R1Z.PV_RunJoin_SemanticScalar50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticPoints50
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPrimitive47
open PV_RunJoin_SemanticScalar50 (raw)
abbrev Points := Array aspis_core.circle.SecureCirclePoint 2#usize

def at (a : Points) (i : Fin 2) : aspis_core.circle.SecureCirclePoint :=
  a.val[i.val]'(by rw [a.property];exact i.isLt)

theorem index (a : Points) (i : Usize) (hi : i.val<2) :
    Array.index_usize a i=ok (at a ⟨i.val,hi⟩) := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok a i hi]
  rfl

theorem point (q : aspis_core.circle.SecureCirclePoint) :
    PV_RunJoin_MaterialInputs49.point (raw q.x) (raw q.y)=q := by
  cases q
  simp only [PV_RunJoin_MaterialInputs49.point,PV_RunJoin_SemanticScalar50.source]

theorem complete (a : Points) :
    PV_RunJoin_MaterialInputs49.points
      (raw (at a 0).x) (raw (at a 0).y) (raw (at a 1).x) (raw (at a 1).y)=a := by
  apply Subtype.ext
  change [PV_RunJoin_MaterialInputs49.point (raw (at a 0).x) (raw (at a 0).y),
    PV_RunJoin_MaterialInputs49.point (raw (at a 1).x) (raw (at a 1).y)]=a.val
  rw [point,point]
  apply List.ext_getElem
  · exact a.property.symm
  · intro j hj hk
    have h : j=0 ∨ j=1 := by simp only [List.length_cons,List.length_nil] at hj;omega
    rcases h with rfl|rfl <;> rfl
#print axioms at
#print axioms index
#print axioms point
#print axioms complete
end R1Z.PV_RunJoin_SemanticPoints50
