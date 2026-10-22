import R1Z.ProverCommitExtraModel51
/-! Extra evaluator to the trace model. Coefficient inputs are explicit. -/
set_option autoImplicit false
namespace R1Z.ProverCommitExtraClaim51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0P.SemSource

theorem exact_result (q : Nat → Old.Q) (hq : ∀ j, j<1024 → Canonical (q j))
    (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (pi : Fin 1024 ≃ Fin 1024) (t : R0P.Trace QM31Exact)
    (coefficients : ∀ j : Fin 1024, decode (q j.val)=coeffsOf pi t 28 j) :
    ∃ z : Old.Q, extra (ProverCommitExtra48.sourceArray q) (ProverCommitNativeQ48.source (p 8))
      (ProverCommitNativeQ48.source (p 9))=ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=R0P.Mask.honestExtra pi t (fun i : Fin 10 => decode (p i.val)) 28 := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitExtraModel51.exact_result q hq (p 8) (p 9)
    (hp _ (by decide)) (hp _ (by decide)) (fun i : Fin 10 => decode (p i.val)) rfl rfl
  refine ⟨z,hz,hcz,?_⟩
  rw [hdz]
  unfold R0P.Mask.honestExtra
  congr 1
  funext j
  exact coefficients j

#print axioms exact_result
end R1Z.ProverCommitExtraClaim51
