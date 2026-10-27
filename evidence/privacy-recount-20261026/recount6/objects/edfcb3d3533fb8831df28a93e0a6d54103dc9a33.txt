import R1Z.ProverRwSuccessQuarticInverseExact
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessQuarticOperations
open Aeneas Aeneas.Std Result
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
abbrev input := ProverRwSuccessQuarticInverseExact.input

theorem mul (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, ProverRwDictionaryTower.qMul (input x) (input y)=.ok (input z) ∧
      Canonical z ∧ decode z=decode x*decode y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeQ48.mul x y hx hy
  refine ⟨z,?_,hc,hd⟩
  change ProverRwDictionaryTower.qMul
    (ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source x))
    (ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source y))=
    .ok (ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source z))
  unfold ProverRwDictionaryTower.qMul
  rw [ProverRwDictionaryTower.native_q_roundtrip,ProverRwDictionaryTower.native_q_roundtrip,hz]
  rfl

theorem sub (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, ProverRwDictionaryTower.qSub (input x) (input y)=.ok (input z) ∧
      Canonical z ∧ decode z=decode x-decode y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeQ48.sub x y hx hy
  refine ⟨z,?_,hc,hd⟩
  change ProverRwDictionaryTower.qSub
    (ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source x))
    (ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source y))=
    .ok (ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source z))
  unfold ProverRwDictionaryTower.qSub
  rw [ProverRwDictionaryTower.native_q_roundtrip,ProverRwDictionaryTower.native_q_roundtrip,hz]
  rfl

theorem neg (x : Old.Q) (hx : Canonical x) :
    ∃ z : Old.Q, ProverRwSuccessInverseInstall.Src.qNeg (input x)=.ok (input z) ∧
      Canonical z ∧ decode z= -decode x := by
  obtain ⟨a,ha,hca,hva⟩ := ProverRwSuccessComplexOperations.neg x.c0 hx.1
  obtain ⟨b,hb,hcb,hvb⟩ := ProverRwSuccessComplexOperations.neg x.c1 hx.2
  unfold ProverRwSuccessComplexOperations.S.neg ProverRwSuccessComplexOperations.input at ha hb
  refine ⟨⟨a,b⟩,?_,⟨hca,hcb⟩,?_⟩
  · simp only [input,ProverRwSuccessQuarticInverseExact.input,
      ProverRwSuccessInverseInstall.Src.qNeg,ProverRwSuccessInverseSource.field.QM31.neg,
      ha,hb,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · exact hva
    · exact hvb
#print axioms mul
#print axioms sub
#print axioms neg
end R1Z.ProverRwSuccessQuarticOperations
