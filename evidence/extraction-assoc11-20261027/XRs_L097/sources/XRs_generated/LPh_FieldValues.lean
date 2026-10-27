import JFv_RawExtractedSemanticCallOpsV20
import ExtractedMaskBasisComponents

set_option autoImplicit false
namespace AspisR1.LPh
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

abbrev P := AspisR1.ExtractedMaskTowerAdd.P
abbrev CanonC (x : GenC) := AspisR1.ExtractedMaskTowerAdd.CanonicalCM (genCToProbe x)
abbrev CanonQ (x : GenQ) := AspisR1.ExtractedMaskTowerAdd.CanonicalQM (genQToProbe x)

def probeQToGen (x : ProbeQ) : GenQ := ⟨probeCToGen x.c0, probeCToGen x.c1⟩

theorem q_roundtrip (x : GenQ) : probeQToGen (genQToProbe x) = x := by
  cases x with | mk a b => cases a; cases b; rfl

theorem reflect_ok {A B : Type} (f : A → B) (g : B → A)
    (roundtrip : ∀ x, g (f x) = x) (r : Result A) (z : B)
    (h : resultMap f r = ok z) : r = ok (g z) := by
  cases r with
  | ok x =>
    have e : f x = z := Result.ok.inj h
    rw [← e, roundtrip]
  | fail e => cases h
  | div => cases h

theorem m31_mul_value (x y : U32) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y = ok z ∧
      z.val = (x.val * y.val) % P ∧ z.val < P := by
  rw [generated_m31_mul_eq_probe]
  exact AspisR1.ExtractedMaskReducer.current_mul_mod x y

theorem cm31_mul_value (x y : GenC) (hx : CanonC x) (hy : CanonC y) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul x y = ok z ∧
      CanonC z ∧
      z.a.val = AspisR1.ExtractedMaskCM31Mul.realWord x.a.val x.b.val y.a.val y.b.val ∧
      z.b.val = AspisR1.ExtractedMaskCM31Mul.imagWord x.a.val x.b.val y.a.val y.b.val := by
  obtain ⟨z, hz, hc, ha, hb⟩ :=
    AspisR1.ExtractedMaskCM31Mul.current_mul_words (genCToProbe x) (genCToProbe y) hx hy
  have h := reflect_ok genCToProbe probeCToGen probeCToGen_genCToProbe
    _ z ((generated_cm_mul_eq_probe x y).trans hz)
  exact ⟨probeCToGen z, h, hc, ha, hb⟩

theorem qm31_mul_value (x y : GenQ) (hx : CanonQ x) (hy : CanonQ y) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y = ok z ∧
      CanonQ z ∧ AspisR1.ExtractedMaskQM31Mul.wordsQM (genQToProbe z) =
        AspisR1.ExtractedMaskQM31Mul.qmMulWords
          (AspisR1.ExtractedMaskQM31Mul.wordsQM (genQToProbe x))
          (AspisR1.ExtractedMaskQM31Mul.wordsQM (genQToProbe y)) := by
  obtain ⟨z, hz, hc, hv⟩ :=
    AspisR1.ExtractedMaskQM31Mul.current_qm_mul_words (genQToProbe x) (genQToProbe y) hx hy
  have h := reflect_ok genQToProbe probeQToGen q_roundtrip
    _ z ((generated_qm_mul_eq_probe x y).trans hz)
  exact ⟨probeQToGen z, h, hc, hv⟩

theorem mul_by_r_value (x : GenC) (hx : CanonC x) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.mul_by_r x = ok z ∧
      CanonC z ∧ AspisR1.ExtractedMaskTowerAdd.wordsCM (genCToProbe z) =
        AspisR1.ExtractedMaskQM31Mul.rWords
          (AspisR1.ExtractedMaskTowerAdd.wordsCM (genCToProbe x)) := by
  obtain ⟨z, hz, hc, hv⟩ :=
    AspisR1.ExtractedMaskBasisComponents.current_cm31_mul_r_words (genCToProbe x) hx
  rw [AspisR1.ExtractedMaskBasisComponents.cm31_mul_r_eq_mul_by_r] at hz
  have h := reflect_ok genCToProbe probeCToGen probeCToGen_genCToProbe
    _ z ((generated_mul_by_r_eq_probe x).trans hz)
  exact ⟨probeCToGen z, h, hc, hv⟩

#print axioms q_roundtrip
#print axioms reflect_ok
#print axioms m31_mul_value
#print axioms cm31_mul_value
#print axioms qm31_mul_value
#print axioms mul_by_r_value
end AspisR1.LPh
