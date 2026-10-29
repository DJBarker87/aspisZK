import R1Z.PV_RunJoin_SemanticClaimPoint50
import R1Z.PV_RunJoin_SemanticMaterialInputs50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_TwoPointFields51
open Aeneas Aeneas.Std ProverRwFull
open PV_RunJoin_SemanticMaterialInputs50

theorem first (a b : aspis_core.circle.SecureCirclePoint) :
    PV_RunJoin_SemanticPoints50.read (Array.make 2#usize [a,b]) 0=a := rfl

theorem second (a b : aspis_core.circle.SecureCirclePoint) :
    PV_RunJoin_SemanticPoints50.read (Array.make 2#usize [a,b]) 1=b := rfl

theorem raw (s : Sem) (a b : aspis_core.circle.SecureCirclePoint) (h : s.z=Array.make 2#usize [a,b]) :
    x0 s=PV_RunJoin_SemanticScalar50.raw a.x ∧ y0 s=PV_RunJoin_SemanticScalar50.raw a.y ∧
    x1 s=PV_RunJoin_SemanticScalar50.raw b.x ∧ y1 s=PV_RunJoin_SemanticScalar50.raw b.y := by
  unfold x0 y0 x1 y1
  rw [h,first,second]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem claim (s : Sem) (a b : aspis_core.circle.SecureCirclePoint) (h : s.z=Array.make 2#usize [a,b]) :
    PV_RunJoin_SemanticClaimPoint50.point s.z=
      ⟨ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded
        (ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw b.x))),
       ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded
        (ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw b.y)))⟩ := by
  rw [h]
  rfl
#print axioms first
#print axioms second
#print axioms raw
#print axioms claim
end R1Z.PV_RunJoin_TwoPointFields51
