import ExtractedMaskQM31Square
import ExtractedMaskQM31Exact
import AspisV8R17.QM31WordTower

/-! Exact-tower adapter for the already checked current QM31 square word
contract. This composes operation-level results only; it makes no caller or
source-refinement claim. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskQM31SquareExact

open Aeneas.Std

abbrev QM := AspisR1.ExtractedMaskQM31Square.QM
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact

def decode (x : QM) : Exact := AspisR1.ExtractedMaskQM31Exact.decode x

theorem current_qm_square_exact (x : QM)
    (hx : CanonicalQM x) :
    ∃ z : QM,
      AspisR1SelectedMaskProbe.field.QM31.square x = .ok z ∧
      CanonicalQM z ∧ decode z = decode x * decode x := by
  obtain ⟨z, hz, hcanon, hwords⟩ :=
    AspisR1.ExtractedMaskQM31Square.current_square_words x hx
  refine ⟨z, hz, hcanon, ?_⟩
  change AspisV8R17.QM31WordTower.decodeQ
      (AspisR1.ExtractedMaskQM31Mul.wordsQM z) =
    AspisV8R17.QM31WordTower.decodeQ
      (AspisR1.ExtractedMaskQM31Mul.wordsQM x) *
      AspisV8R17.QM31WordTower.decodeQ
        (AspisR1.ExtractedMaskQM31Mul.wordsQM x)
  have hword :
      AspisR1.ExtractedMaskQM31Mul.wordsQM z =
        AspisV8R17.GeneratedQM31Products.qmSquareWords
          (AspisR1.ExtractedMaskQM31Mul.wordsQM x) := by
    change AspisR1.ExtractedMaskQM31Mul.wordsQM z =
      AspisV8R17.GeneratedQM31Products.qmSquareWords
        (AspisR1.ExtractedMaskQM31Mul.wordsQM x) at hwords
    exact hwords
  rw [hword]
  exact AspisV8R17.QM31WordTower.decode_square _

#print axioms current_qm_square_exact

end AspisR1.ExtractedMaskQM31SquareExact
