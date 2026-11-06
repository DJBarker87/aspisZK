import NKM_SpecMatching
import JFv_RawExtractedSemanticCallOpsV20
set_option autoImplicit false
noncomputable section
namespace NKM_EmittedMul
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open NKM_FieldLaws

def toGen (x : NKM_circle.field.QM31) : GenQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toLocal (x : GenQ) : NKM_circle.field.QM31 := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

theorem gen_roundtrip (x : GenQ) : toGen (toLocal x)=x := by cases x;rfl

theorem emitted_product (x y : GenQ)
 (hx : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (genQToProbe x))
 (hy : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (genQToProbe y)) :
 ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y=ok z ∧
 AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (genQToProbe z) ∧
 AspisR1.ExtractedMaskQM31Exact.decode (genQToProbe z)=
 AspisR1.ExtractedMaskQM31Exact.decode (genQToProbe x)*AspisR1.ExtractedMaskQM31Exact.decode (genQToProbe y) := by
 obtain ⟨z,hz,hc,hd⟩ := AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact _ _ hx hy
 have h:=generated_qm_mul_eq_probe x y
 rw [hz] at h
 cases hr:AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y with
 | fail e => simp only [hr,resultMap] at h;cases h
 | div => simp only [hr,resultMap] at h;cases h
 | ok out =>
  simp only [hr,resultMap,Result.ok.injEq] at h
  refine ⟨out,hr,?_,?_⟩
  · rw [h];exact hc
  · rw [h];exact hd

/-- Named exact-value law on canonical emitted operands, directly from JFv's generated-body equality. -/
theorem emitted_exact (x y : GenQ)
 (hx : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (genQToProbe x))
 (hy : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (genQToProbe y)) :
 AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y=
 ok (toGen (NKM_SpecLaws.product (toLocal x) (toLocal y))) := by
 obtain ⟨z,hz,hc,hd⟩:=emitted_product x y hx hy
 have canon : Canon (toLocal z) := hc
 have decoded : NKM_SpecLaws.decode (toLocal z)=
  NKM_SpecLaws.decode (toLocal x)*NKM_SpecLaws.decode (toLocal y) := hd
 have he : toLocal z=NKM_SpecLaws.product (toLocal x) (toLocal y) := by
  rw [NKM_SpecLaws.product,←decoded]
  exact (roundtrip _ canon).symm
 rw [hz,←he,gen_roundtrip]

#print axioms gen_roundtrip
#print axioms emitted_product
#print axioms emitted_exact
end NKM_EmittedMul
end
