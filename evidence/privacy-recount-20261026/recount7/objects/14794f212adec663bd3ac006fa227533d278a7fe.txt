import R1Z.ProverRwSuccessComplexInverseExact
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessComplexOperations
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49
open AspisV8R15.ExactTowerBase
abbrev input := ProverRwSuccessComplexInverseExact.input
namespace S
abbrev mul := ProverRwSuccessInverseSource.field.CM31.mul
abbrev sub := ProverRwSuccessInverseSource.field.CM31.sub
abbrev neg := ProverRwSuccessInverseSource.field.CM31.neg
end S

theorem mul (x y : Old.C) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.C, S.mul (input x) (input y)=.ok (input z) ∧
      Canonical z ∧ value z=value x*value y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeC49.mul x y hx hy
  refine ⟨z,?_,hc,hd⟩
  unfold S.mul ProverRwSuccessInverseSource.field.CM31.mul input ProverRwSuccessComplexInverseExact.input
  rw [ProverRwDictionaryTower.native_c_roundtrip,ProverRwDictionaryTower.native_c_roundtrip,hz]
  rfl

theorem sub (x y : Old.C) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.C, S.sub (input x) (input y)=.ok (input z) ∧
      Canonical z ∧ value z=value x-value y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeC49.sub x y hx hy
  refine ⟨z,?_,hc,hd⟩
  unfold S.sub ProverRwSuccessInverseSource.field.CM31.sub input ProverRwSuccessComplexInverseExact.input
  rw [ProverRwDictionaryTower.native_c_roundtrip,ProverRwDictionaryTower.native_c_roundtrip,hz]
  rfl

theorem neg (x : Old.C) (hx : Canonical x) :
    ∃ z : Old.C, S.neg (input x)=.ok (input z) ∧
      Canonical z ∧ value z= -value x := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeNeg49.neg x hx
  refine ⟨z,?_,hc,hd⟩
  unfold S.neg ProverRwSuccessInverseSource.field.CM31.neg input ProverRwSuccessComplexInverseExact.input
  rw [ProverRwDictionaryTower.native_c_roundtrip,hz]
  rfl
#print axioms mul
#print axioms sub
#print axioms neg
end R1Z.ProverRwSuccessComplexOperations
