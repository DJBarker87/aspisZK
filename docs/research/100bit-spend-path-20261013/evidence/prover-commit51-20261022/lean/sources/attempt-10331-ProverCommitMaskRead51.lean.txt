import R1Z.ProverCommitMaskColumns51
import R1Z.ProverCommitMaskCaller51
import R0Z.PayloadSplit
/-! Mask point function from every tape-column MLE, with no read-result premise. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaskRead51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0P.SemSource
variable {F : Subfield QM31Exact}

attribute [local irreducible] ProverCommitNativeQ48.source ProverCommitQArray48.array
  mask_coeff51.eval linear50.eval mask_horner50.eval mask_finish50.eval
  ProverCommitMaskColumns51.value

def run (p : Array field.QM31 10#usize)
    (c : Array (Array field.QM31 1024#usize) 26#usize)
    (g : Array field.QM31 1024#usize) : Result field.QM31 := do
  let inputs ← mask_columns51.eval p c
  let gv ← mle50.mle p g
  let coefficients ← mask_coeff51.eval inputs (ProverCommitMaskWrites51.exponents ProverCommitMaskProducer51.word)
  let (l0,l16) ← linear50.eval p
  let shared ← mask_horner50.eval coefficients l0
  mask_finish50.eval shared l16 gv

theorem claims_value (p : Nat → Old.Q) (c : Nat → Nat → Old.Q)
    (t : R0P.Trace QM31Exact) (ht : ∀ l : Fin 29, ∀ j : Fin 1024, decode (c l.val j.val)=t l j)
    (i : Fin 29) : ProverCommitMaskColumns51.value p c i.val=
      honestClaims t (fun j : Fin 10 => decode (p j.val)) 0 i := by
  unfold ProverCommitMaskColumns51.value honestClaims
  change AspisR0.RoundNormalization.dot _ _=AspisR0.RoundNormalization.dot _ _
  congr 1
  funext j
  exact ht i j

theorem exact_result (B : R0P.PackBasis F)
    (hi : B.i=⟨ProverCommitTower50.ci,0⟩) (hu : B.u=⟨0,1⟩)
    (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (c : Nat → Nat → Old.Q) (hc : ∀ i, i<29 → ∀ j, j<1024 → Canonical (c i j)) :
    ∃ z : Old.Q, run (ProverCommitQArray48.array 10#usize p) (ProverCommitMaskColumns51.columns c)
      (ProverCommitQArray48.array 1024#usize (c 27))=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=R0P.Mask.maskValue B
        (fun i : Fin 16 => ProverCommitMaskColumns51.value p c i.val)
        (fun i : Fin 10 => ProverCommitMaskColumns51.value p c (16+i.val))
        (ProverCommitMaskColumns51.value p c 27) (fun i : Fin 10 => decode (p i.val)) := by
  obtain ⟨inputs,hinputs,hcinputs,hdinputs⟩ := ProverCommitMaskColumns51.exact_result p hp c (fun i h => hc i (by omega))
  obtain ⟨g,hg,hcg,hdg⟩ := ProverCommitMle50.model_result p (c 27) hp (hc 27 (by decide))
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitMaskCaller51.exact_result B hi hu inputs p g hcinputs hp hcg
  refine ⟨z,?_,hcz,?_⟩
  · rw [run,hinputs]
    simp only [bind_tc_ok,hg]
    exact hz
  · have hfirst : (fun i : Fin 16 => decode (inputs i.val))=
        (fun i : Fin 16 => ProverCommitMaskColumns51.value p c i.val) := by
      funext i;exact hdinputs i.val (by omega)
    have hsecond : (fun i : Fin 10 => decode (inputs (16+i.val)))=
        (fun i : Fin 10 => ProverCommitMaskColumns51.value p c (16+i.val)) := by
      funext i;exact hdinputs (16+i.val) (by have := i.isLt;omega)
    have hgv : decode g=ProverCommitMaskColumns51.value p c 27 := by
      simpa only [ProverCommitMaskColumns51.value] using hdg
    rw [hfirst,hsecond,hgv] at hdz
    exact hdz

#print axioms claims_value
#print axioms exact_result
end R1Z.ProverCommitMaskRead51
