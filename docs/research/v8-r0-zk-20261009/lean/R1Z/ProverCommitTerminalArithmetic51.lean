import R1Z.ProverCommitTerminalSuffix51
/-! Equality-product and suffix composed. The composition producer remains upstream. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTerminalArithmetic51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

def run (zc point : Array field.QM31 10#usize) (composition h1 active mu : field.QM31) : Result field.QM31 := do
  let eq ← terminal_eq51.eval zc point
  terminal_eq51.suffix eq composition h1 active mu

attribute [local irreducible] ProverCommitNativeQ48.source ProverCommitQArray48.array
  terminal_eq51.eval terminal_eq51.suffix

theorem exact_result (zc point : Nat → Old.Q)
    (hzc : ∀ i, i<10 → Canonical (zc i)) (hpoint : ∀ i, i<10 → Canonical (point i))
    (composition h1 active mu : Old.Q)
    (hcomp : Canonical composition) (hh1 : Canonical h1) (hactive : Canonical active) (hmu : Canonical mu) :
    ∃ z : Old.Q, run (ProverCommitQArray48.array 10#usize zc) (ProverCommitQArray48.array 10#usize point)
      (ProverCommitNativeQ48.source composition) (ProverCommitNativeQ48.source h1)
      (ProverCommitNativeQ48.source active) (ProverCommitNativeQ48.source mu)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=R0P.SemSource.eqValue (fun i : Fin 10 => decode (zc i.val))
        (fun i : Fin 10 => decode (point i.val))*decode composition+decode mu*decode h1+
        (decode mu*decode mu)*((1-decode active)*decode h1) := by
  obtain ⟨eq,heq,hceq,hdeq⟩ := ProverCommitTerminalEquality51.exact_result zc point hzc hpoint
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitTerminalSuffix51.exact_result eq composition h1 active mu hceq hcomp hh1 hactive hmu
  refine ⟨z,?_,hcz,?_⟩
  · simp only [run,heq,hz,bind_tc_ok]
  · rw [hdz,hdeq]

theorem zero_helper (zc point : Nat → Old.Q)
    (hzc : ∀ i, i<10 → Canonical (zc i)) (hpoint : ∀ i, i<10 → Canonical (point i))
    (composition active mu : Old.Q)
    (hcomp : Canonical composition) (hactive : Canonical active) (hmu : Canonical mu) :
    ∃ z : Old.Q, run (ProverCommitQArray48.array 10#usize zc) (ProverCommitQArray48.array 10#usize point)
      (ProverCommitNativeQ48.source composition) (ProverCommitNativeQ48.source zero)
      (ProverCommitNativeQ48.source active) (ProverCommitNativeQ48.source mu)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=R0P.SemSource.eqValue (fun i : Fin 10 => decode (zc i.val))
        (fun i : Fin 10 => decode (point i.val))*decode composition := by
  obtain ⟨z,hz,hcz,hdz⟩ := exact_result zc point hzc hpoint composition zero active mu hcomp zero_canonical hactive hmu
  refine ⟨z,hz,hcz,?_⟩
  simpa only [zero_decode,mul_zero,add_zero] using hdz

#print axioms exact_result
#print axioms zero_helper
end R1Z.ProverCommitTerminalArithmetic51
