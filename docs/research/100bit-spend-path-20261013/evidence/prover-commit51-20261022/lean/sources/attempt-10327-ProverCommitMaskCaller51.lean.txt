import R1Z.ProverCommitMaskProducer51
import R1Z.ProverCommitMaskArithmetic51
/-! Complete coefficient production and selected-mask arithmetic composition. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaskCaller51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
variable {F : Subfield QM31Exact}
attribute [local irreducible] ProverCommitNativeQ48.source ProverCommitQArray48.array
  linear50.eval mask_horner50.eval mask_finish50.eval mask_coeff51.eval

theorem exact_result (B : R0P.PackBasis F)
    (hi : B.i=⟨ProverCommitTower50.ci,0⟩) (hu : B.u=⟨0,1⟩)
    (c p : Nat → Old.Q) (g : Old.Q)
    (hc : ∀ i, i<26 → Canonical (c i)) (hp : ∀ i, i<10 → Canonical (p i)) (hg : Canonical g) :
    ∃ z : Old.Q, (do
      let coefficients ← mask_coeff51.eval (ProverCommitQArray48.array 26#usize c)
        (ProverCommitMaskWrites51.exponents ProverCommitMaskProducer51.word)
      let (l0,l16) ← linear50.eval (ProverCommitQArray48.array 10#usize p)
      let shared ← mask_horner50.eval coefficients l0
      mask_finish50.eval shared l16 (ProverCommitNativeQ48.source g))=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=R0P.Mask.maskValue B
        (fun i : Fin 16 => decode (c i.val)) (fun i : Fin 10 => decode (c (16+i.val)))
        (decode g) (fun i : Fin 10 => decode (p i.val)) := by
  obtain ⟨q,hq,hcq,hdq⟩ := ProverCommitMaskProducer51.exact_result B hi hu c hc
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitMaskArithmetic51.caller B
    (fun i : Fin 16 => decode (c i.val)) (fun i : Fin 10 => decode (c (16+i.val)))
    p q g hp hcq hg (fun k _ => hdq k)
  refine ⟨z,?_,hcz,hdz⟩
  rw [hq]
  exact hz

#print axioms exact_result
end R1Z.ProverCommitMaskCaller51
