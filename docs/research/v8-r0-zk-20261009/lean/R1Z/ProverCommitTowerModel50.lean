import R1Z.ProverCommitTower50
import R0P.MaskValue
/-! Explicit model-basis adapter for the optimized source tower helper.
Only input representation equations for B.i and B.u are retained. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTowerModel50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
variable {F : Subfield QM31Exact}

theorem basis_model (B : R0P.PackBasis F)
    (hi : B.i=⟨ProverCommitTower50.ci,0⟩) (hu : B.u=⟨0,1⟩) (j : Fin 4) :
    ProverCommitTower50.basis j=R0P.Mask.towerBasis B j := by
  fin_cases j
  · change (1:QM31Exact)=1;rfl
  · change (⟨ProverCommitTower50.ci,0⟩ : QM31Exact)=B.i
    exact hi.symm
  · change (⟨0,1⟩ : QM31Exact)=B.u
    exact hu.symm
  · change (⟨0,ProverCommitTower50.ci⟩ : QM31Exact)=B.i*B.u
    rw [hi,hu]
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]

theorem exact_result (B : R0P.PackBasis F)
    (hi : B.i=⟨ProverCommitTower50.ci,0⟩) (hu : B.u=⟨0,1⟩)
    (x : Old.Q) (hx : Canonical x) (j : Fin 4) (word : U8) (hw : word.val=j.val) :
    ∃ z : Old.Q, tower50.mul (ProverCommitNativeQ48.source x) word=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=R0P.Mask.mulTowerBasis B (decode x) j := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitTower50.mul x hx j word hw
  rw [basis_model B hi hu] at hdz
  exact ⟨z,hz,hcz,hdz⟩

#print axioms basis_model
#print axioms exact_result
end R1Z.ProverCommitTowerModel50
