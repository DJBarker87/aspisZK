import ExtractedMaskQM31Mul
import ExtractedMaskCM31SquareEqMul
import AspisV8R17.QM31WordFormulas

/-! Current extracted QM31 square composed from current CM31 operations. The
word contract is the retained pure `qmSquareWords` identity; this is still an
operation-level result, not a verifier-caller theorem. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskQM31Square

open Aeneas.Std Result

abbrev P := AspisR1.ExtractedMaskTowerAdd.P
abbrev CM := AspisR1.ExtractedMaskCM31Mul.CM
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev WordPair := AspisR1.ExtractedMaskQM31Mul.WordPair

private def wordsCM (x : CM) : WordPair := (x.a.val, x.b.val)
private def wordsQM (x : QM) : WordPair × WordPair :=
  (wordsCM x.c0, wordsCM x.c1)

private theorem cm_add (x y : CM)
    (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalCM x)
    (hy : AspisR1.ExtractedMaskTowerAdd.CanonicalCM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.add x y = .ok z ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalCM z ∧
      wordsCM z = AspisR1.ExtractedMaskQM31Mul.addWords
        (wordsCM x) (wordsCM y) := by
  obtain ⟨z, hz, hc, ha, hb⟩ :=
    AspisR1.ExtractedMaskTowerAdd.current_cm_add_mod x y hx hy
  exact ⟨z, hz, hc, Prod.ext ha hb⟩

private theorem cm_mul (x y : CM)
    (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalCM x)
    (hy : AspisR1.ExtractedMaskTowerAdd.CanonicalCM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.mul x y = .ok z ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalCM z ∧
      wordsCM z = AspisR1.ExtractedMaskQM31Mul.mulWords
        (wordsCM x) (wordsCM y) := by
  obtain ⟨z, hz, hc, ha, hb⟩ :=
    AspisR1.ExtractedMaskCM31Mul.current_mul_words x y hx hy
  exact ⟨z, hz, hc, Prod.ext ha hb⟩

private theorem cm_r (x : CM)
    (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalCM x) :
    ∃ z, AspisR1SelectedMaskProbe.field.mul_by_r x = .ok z ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalCM z ∧
      wordsCM z = AspisR1.ExtractedMaskQM31Mul.rWords (wordsCM x) := by
  obtain ⟨a2, ea2, va2, ca2⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a, ea, va, ca⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2, eb2, vb2, cb2⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b, eb, vb, cb⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a b2 hx.1 cb2
  refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.mul_by_r,
      AspisR1SelectedMaskProbe.field.M31.double,
      ea2, ea, eb2, eb, bind_tc_ok]
  · change (a.val, b.val) = _
    simp only [AspisR1.ExtractedMaskQM31Mul.rWords, wordsCM]
    exact Prod.ext (by simpa only [va2] using va)
      (by simpa only [vb2] using vb)

theorem current_square_words (x : QM)
    (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalQM x) :
    ∃ z : QM,
      AspisR1SelectedMaskProbe.field.QM31.square x = .ok z ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM z ∧
      wordsQM z = AspisV8R17.GeneratedQM31Products.qmSquareWords
        (wordsQM x) := by
  obtain ⟨a, ea, ca, va⟩ := cm_mul x.c0 x.c0 hx.1 hx.1
  obtain ⟨b, eb, cb, vb⟩ := cm_mul x.c1 x.c1 hx.2 hx.2
  have esa := AspisR1.ExtractedMaskCM31SquareEqMul.current_square_eq_mul_self
    x.c0 hx.1
  have esb := AspisR1.ExtractedMaskCM31SquareEqMul.current_square_eq_mul_self
    x.c1 hx.2
  obtain ⟨r, er, cr, vr⟩ := cm_r b cb
  obtain ⟨lo, elo, clo, vlo⟩ := cm_add a r ca cr
  obtain ⟨m, em, cm, vm⟩ := cm_mul x.c0 x.c1 hx.1 hx.2
  obtain ⟨hi, ehi, chi, vhi⟩ := cm_add m m cm cm
  refine ⟨⟨lo, hi⟩, ?_, ⟨clo, chi⟩, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.QM31.square,
      AspisR1SelectedMaskProbe.field.CM31.double,
      esa, esb, ea, eb, er, elo, em, ehi, bind_tc_ok]
  · change (wordsCM lo, wordsCM hi) = _
    rw [vhi, vlo, vr, va, vb, vm]
    rfl

#print axioms current_square_words

end AspisR1.ExtractedMaskQM31Square
