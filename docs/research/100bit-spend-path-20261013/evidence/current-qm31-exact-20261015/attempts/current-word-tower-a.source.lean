import ExtractedCurrentQM31Mul
import AspisV8R17.QM31WordTower

/-!
Adapter from current extracted QM31 word operations to the historical pure
quadratic-tower decoder. No runtime definitions or source-correspondence claims
are added here.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedCurrentQM31Tower

abbrev CurrentQM := AspisR1Qm31ArithmeticProbe.field.QM31
abbrev CurrentCanonicalQM := AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
abbrev WordPair := AspisR1.ExtractedCurrentQM31Mul.WordPair

/-- Interpret the four current canonical U32 coordinates in the pure old
word-to-tower model. -/
def decode (x : CurrentQM) : AspisV8R17.QM31WordTower.Q :=
  AspisV8R17.QM31WordTower.decodeQ
    (AspisR1.ExtractedCurrentQM31Mul.wordsQM x)

private theorem current_qmMulWords_eq_old
    (x y : WordPair × WordPair) :
    AspisR1.ExtractedCurrentQM31Mul.qmMulWords x y =
      AspisV8R17.GeneratedQM31Products.qmMulWords x y := by
  rfl

theorem current_qm_add_exact
    (x y : CurrentQM)
    (hx : CurrentCanonicalQM x) (hy : CurrentCanonicalQM y) :
    ∃ z : CurrentQM,
      AspisR1Qm31ArithmeticProbe.field.QM31.add x y = .ok z ∧
      CurrentCanonicalQM z ∧ decode z = decode x + decode y := by
  obtain ⟨z, hz, hcanon, hcurrentWords⟩ :=
    AspisR1.ExtractedCurrentTowerAdd.current_qm_add_mod x y hx hy
  have hword :
      AspisR1.ExtractedCurrentQM31Mul.wordsQM z =
        AspisV8R17.GeneratedQM31Linear.qmAddWords
          (AspisR1.ExtractedCurrentQM31Mul.wordsQM x)
          (AspisR1.ExtractedCurrentQM31Mul.wordsQM y) := by
    exact hcurrentWords
  refine ⟨z, hz, hcanon, ?_⟩
  change AspisV8R17.QM31WordTower.decodeQ
      (AspisR1.ExtractedCurrentQM31Mul.wordsQM z) =
    AspisV8R17.QM31WordTower.decodeQ
        (AspisR1.ExtractedCurrentQM31Mul.wordsQM x) +
      AspisV8R17.QM31WordTower.decodeQ
        (AspisR1.ExtractedCurrentQM31Mul.wordsQM y)
  rw [hword]
  exact AspisV8R17.QM31WordTower.decode_add _ _

theorem current_qm_mul_exact
    (x y : CurrentQM)
    (hx : CurrentCanonicalQM x) (hy : CurrentCanonicalQM y) :
    ∃ z : CurrentQM,
      AspisR1Qm31ArithmeticProbe.field.QM31.mul x y = .ok z ∧
      CurrentCanonicalQM z ∧ decode z = decode x * decode y := by
  obtain ⟨z, hz, hcanon, hcurrentWords⟩ :=
    AspisR1.ExtractedCurrentQM31Mul.current_qm_mul_words x y hx hy
  have hword :
      AspisR1.ExtractedCurrentQM31Mul.wordsQM z =
        AspisV8R17.GeneratedQM31Products.qmMulWords
          (AspisR1.ExtractedCurrentQM31Mul.wordsQM x)
          (AspisR1.ExtractedCurrentQM31Mul.wordsQM y) := by
    exact hcurrentWords.trans (current_qmMulWords_eq_old
      (AspisR1.ExtractedCurrentQM31Mul.wordsQM x)
      (AspisR1.ExtractedCurrentQM31Mul.wordsQM y))
  refine ⟨z, hz, hcanon, ?_⟩
  change AspisV8R17.QM31WordTower.decodeQ
      (AspisR1.ExtractedCurrentQM31Mul.wordsQM z) =
    AspisV8R17.QM31WordTower.decodeQ
        (AspisR1.ExtractedCurrentQM31Mul.wordsQM x) *
      AspisV8R17.QM31WordTower.decodeQ
        (AspisR1.ExtractedCurrentQM31Mul.wordsQM y)
  rw [hword]
  exact AspisV8R17.QM31WordTower.decode_mul _ _

#print axioms current_qm_add_exact
#print axioms current_qm_mul_exact

end AspisR1.ExtractedCurrentQM31Tower
