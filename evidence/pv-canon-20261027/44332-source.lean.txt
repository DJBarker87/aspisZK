import R1Z.PV_Canon_ComplexTryInverse
import R1Z.ProverCommitNativeNeg49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem inverse_cmul_safe (x y : aspis_core.field.CM31) (hx : C x) (hy : C y) :
    Safe C (ProverRwSuccessInverseSource.field.CM31.mul x y) := by
  let ox : ProverCommitPrimitive47.Old.C := ⟨x.a,x.b⟩
  let oy : ProverCommitPrimitive47.Old.C := ⟨y.a,y.b⟩
  obtain ⟨z,hz,hc,_⟩ := ProverCommitNativeC49.mul ox oy hx hy
  apply safe_of_total
  refine ⟨⟨z.a,z.b⟩,?_,hc⟩
  change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromC
    (AspisR1ProducerRelease47.field.CM31.mul (ProverCommitNativeC49.source ox)
      (ProverCommitNativeC49.source oy)) = _
  rw [hz]
  rfl
 theorem inverse_cneg_safe (x : aspis_core.field.CM31) (hx : C x) :
    Safe C (ProverRwSuccessInverseSource.field.CM31.neg x) := by
  let ox : ProverCommitPrimitive47.Old.C := ⟨x.a,x.b⟩
  obtain ⟨z,hz,hc,_⟩ := ProverCommitNativeNeg49.neg ox hx
  apply safe_of_total
  refine ⟨⟨z.a,z.b⟩,?_,hc⟩
  change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromC
    (AspisR1ProducerRelease47.field.CM31.neg (ProverCommitNativeC49.source ox)) = _
  rw [hz]
  rfl
#print axioms inverse_cmul_safe
#print axioms inverse_cneg_safe
end R1Z.PV_Canon
