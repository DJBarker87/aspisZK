import R1Z.ProverCommitCircleWeight49
import R1Z.ProverCommitCircleFunctional49
/-! The constructed circle raw weight is the model evaluator's coefficient
functional, including its WideExact embedding. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCircleCaller49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitValueRange47 (embed E)

attribute [local irreducible] ProverCommitEval47.messageEval

theorem embedded_single (j : Fin 1024) :
    (fun i : Fin 1024 => embed ((Pi.single j 1 : Fin 1024 → QM31Exact) i))=(Pi.single j 1 : Fin 1024 → ProverCommitValueRange47.E) := by
  funext i
  by_cases h : i=j
  · subst i;simp only [Pi.single_eq_same,embed,map_one]
  · simp only [Pi.single_eq_of_ne h,embed,map_zero]

theorem raw_message (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) (j : Fin 1024) :
    ∃ z : Old.Q,
      factors.product (ProverCommitQArray48.array 5#usize (ProverCommitCircleWeight49.selected x y hx hy j))
        0#usize 5#u8 field.QM31.ONE=ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=ProverCommitEval47.messageEval (Pi.single j 1) (decode x) (decode y) ∧
      embed (decode z)=ProverCommitEval47.messageEval (Pi.single j 1) (embed (decode x)) (embed (decode y)) := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitCircleWeight49.raw_exact x y hx hy j
  have hd : decode z=ProverCommitEval47.messageEval (Pi.single j 1) (decode x) (decode y) :=
    hdz.trans (ProverCommitCircleFunctional49.message_single j (decode x) (decode y)).symm
  refine ⟨z,hz,hcz,hd,?_⟩
  rw [←embedded_single j,ProverCommitEval47.message_embed,hd]

#print axioms embedded_single
#print axioms raw_message
end R1Z.ProverCommitCircleCaller49
