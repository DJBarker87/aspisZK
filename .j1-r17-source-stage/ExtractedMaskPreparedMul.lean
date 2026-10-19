import ExtractedMaskPreparedComponent
import ExtractedMaskQM31Exact

/-! Execution equality between the extracted prepared multiplier and ordinary
QM31 multiplication, followed by the existing exact-field interpretation. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskPreparedMul
open Aeneas.Std Result
open AspisR1SelectedMaskProbe
open ExtractedMaskPreparedState ExtractedMaskTowerAdd ExtractedMaskArrayThree

private theorem cm_eq_of_words (x y : CM)
    (h : (x.a.val, x.b.val) = (y.a.val, y.b.val)) : x = y := by
  have ha := UScalar.val_eq_imp x.a y.a (congrArg Prod.fst h)
  have hb := UScalar.val_eq_imp x.b y.b (congrArg Prod.snd h)
  cases x with
  | mk xa xb =>
    cases y with
    | mk ya yb =>
      dsimp at ha hb
      cases ha
      cases hb
      rfl

theorem component_eq_mul (a : Component) (x y : CM)
    (hx : CanonicalCM x) (hy : CanonicalCM y) (hp : ComponentFor a x) :
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a, y) = field.CM31.mul x y := by
  obtain ⟨z, hz, _, hv⟩ :=
    ExtractedMaskPreparedComponent.current_component_mul_words a x y hx hy hp
  obtain ⟨w, hw, _, hwa, hwb⟩ := ExtractedMaskCM31Mul.current_mul_words x y hx hy
  have hwv : (w.a.val, w.b.val) = ExtractedMaskQM31Mul.mulWords
      (x.a.val, x.b.val) (y.a.val, y.b.val) := Prod.ext hwa hwb
  have hzw := cm_eq_of_words z w (hv.trans hwv.symm)
  rw [hz, hw, hzw]

theorem prepared_mul_eq (p : Prepared) (x y : QM)
    (hx : CanonicalQM x) (hy : CanonicalQM y) (hp : PreparedFor p x) :
    field.PreparedQm31Multiplier.mul p y = field.QM31.mul x y := by
  obtain ⟨t, a, b, c, ht, hct, ha, hb, hc, harr⟩ := hp
  obtain ⟨s, hs, hcs, _, _⟩ := current_cm_add_mod y.c0 y.c1 hy.1 hy.2
  have hpa := component_eq_mul a x.c0 y.c0 hx.1 hy.1 ha
  have hpb := component_eq_mul b x.c1 y.c1 hx.2 hy.2 hb
  have hpc := component_eq_mul c t s hct hcs hc
  simp only [field.PreparedQm31Multiplier.mul, harr, index0, index1, index2,
    hpa, hpb, hs, hpc, bind_tc_ok, field.QM31.mul, ht]

theorem prepared_mul_exact (p : Prepared) (x y : QM)
    (hx : CanonicalQM x) (hy : CanonicalQM y) (hp : PreparedFor p x) :
    ∃ z : QM, field.PreparedQm31Multiplier.mul p y = .ok z ∧
      CanonicalQM z ∧ ExtractedMaskQM31Exact.decode z =
        ExtractedMaskQM31Exact.decode x * ExtractedMaskQM31Exact.decode y := by
  rw [prepared_mul_eq p x y hx hy hp]
  exact ExtractedMaskQM31Exact.current_qm_mul_exact x y hx hy

theorem current_prepared_correct (x y : QM)
    (hx : CanonicalQM x) (hy : CanonicalQM y) :
    ∃ p : Prepared, ∃ z : QM,
      field.PreparedQm31Multiplier.new x = .ok p ∧
      field.PreparedQm31Multiplier.mul p y = .ok z ∧
      CanonicalQM z ∧ ExtractedMaskQM31Exact.decode z =
        ExtractedMaskQM31Exact.decode x * ExtractedMaskQM31Exact.decode y := by
  obtain ⟨p, hp, hprepared⟩ := current_prepared_new x hx
  obtain ⟨z, hz, hc, hv⟩ := prepared_mul_exact p x y hx hy hprepared
  exact ⟨p, z, hp, hz, hc, hv⟩

#print axioms component_eq_mul
#print axioms prepared_mul_eq
#print axioms prepared_mul_exact
#print axioms current_prepared_correct
end AspisR1.ExtractedMaskPreparedMul
