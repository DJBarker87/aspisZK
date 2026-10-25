import ExtractedMaskBasisComponents
import ExtractedMaskQM31Mul
import ExtractedMaskTowerAdd
import AspisR1SelectedMaskProbe.Funs

/-! Canonical-input output and word mapping for the four actual extracted
QM31 tower-basis branches. This is an operation-level contract only. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskTowerBasis

open Aeneas.Std Result Error

abbrev P : Nat := AspisR1.ExtractedMaskTowerAdd.P
abbrev CM := AspisR1SelectedMaskProbe.field.CM31
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev WordPair := Nat × Nat
abbrev WordQM := WordPair × WordPair

def iWords (x : WordPair) : WordPair := ((P - x.2) % P, x.1)

def basisWords (x : WordQM) (coordinate : Nat) : WordQM :=
  match coordinate with
  | 0 => x
  | 1 => (iWords x.1, iWords x.2)
  | 2 => (AspisR1.ExtractedMaskQM31Mul.rWords x.2, x.1)
  | 3 => (iWords (AspisR1.ExtractedMaskQM31Mul.rWords x.2), iWords x.1)
  | _ => x

theorem current_mul_tower_basis_words (x : QM) (coordinate : Usize)
    (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalQM x)
    (hcoord : coordinate.val < 4) :
    ∃ z : QM,
      AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis x coordinate = .ok z ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM z ∧
      AspisR1.ExtractedMaskTowerAdd.wordsQM z =
        basisWords (AspisR1.ExtractedMaskTowerAdd.wordsQM x) coordinate.val := by
  have hcases : coordinate.val = 0 ∨ coordinate.val = 1 ∨
      coordinate.val = 2 ∨ coordinate.val = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · refine ⟨x, ?_, hx, ?_⟩
    · simp [AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis, h0]
    · simp [basisWords, h0]
  · obtain ⟨a, ea, ca, va⟩ :=
      AspisR1.ExtractedMaskBasisComponents.current_cm31_mul_i_words x.c0 hx.1
    obtain ⟨b, eb, cb, vb⟩ :=
      AspisR1.ExtractedMaskBasisComponents.current_cm31_mul_i_words x.c1 hx.2
    refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
    · simp only [AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis,
        h1, ea, eb, bind_tc_ok]
    · simp only [basisWords, h1]
      change (AspisR1.ExtractedMaskTowerAdd.wordsCM a,
        AspisR1.ExtractedMaskTowerAdd.wordsCM b) =
        (iWords (AspisR1.ExtractedMaskTowerAdd.wordsCM x.c0),
          iWords (AspisR1.ExtractedMaskTowerAdd.wordsCM x.c1))
      exact Prod.ext va vb
  · obtain ⟨r, er, cr, vr⟩ :=
      AspisR1.ExtractedMaskBasisComponents.current_cm31_mul_r_words x.c1 hx.2
    refine ⟨⟨r, x.c0⟩, ?_, ⟨cr, hx.1⟩, ?_⟩
    · simp only [AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis,
        h2, er, bind_tc_ok]
    · simp only [basisWords, h2]
      change (AspisR1.ExtractedMaskTowerAdd.wordsCM r,
        AspisR1.ExtractedMaskTowerAdd.wordsCM x.c0) =
        (AspisR1.ExtractedMaskQM31Mul.rWords
          (AspisR1.ExtractedMaskTowerAdd.wordsCM x.c1),
          AspisR1.ExtractedMaskTowerAdd.wordsCM x.c0)
      exact Prod.ext vr rfl
  · obtain ⟨r, er, cr, vr⟩ :=
      AspisR1.ExtractedMaskBasisComponents.current_cm31_mul_r_words x.c1 hx.2
    obtain ⟨a, ea, ca, va⟩ :=
      AspisR1.ExtractedMaskBasisComponents.current_cm31_mul_i_words r cr
    obtain ⟨b, eb, cb, vb⟩ :=
      AspisR1.ExtractedMaskBasisComponents.current_cm31_mul_i_words x.c0 hx.1
    refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
    · simp only [AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis,
        h3, er, ea, eb, bind_tc_ok]
    · simp only [basisWords, h3]
      change (AspisR1.ExtractedMaskTowerAdd.wordsCM a,
        AspisR1.ExtractedMaskTowerAdd.wordsCM b) =
        (iWords (AspisR1.ExtractedMaskQM31Mul.rWords
          (AspisR1.ExtractedMaskTowerAdd.wordsCM x.c1)),
          iWords (AspisR1.ExtractedMaskTowerAdd.wordsCM x.c0))
      apply Prod.ext _ vb
      calc
        AspisR1.ExtractedMaskTowerAdd.wordsCM a =
            iWords (AspisR1.ExtractedMaskTowerAdd.wordsCM r) := va
        _ = iWords (AspisR1.ExtractedMaskQM31Mul.rWords
            (AspisR1.ExtractedMaskTowerAdd.wordsCM x.c1)) := congrArg iWords vr

#print axioms current_mul_tower_basis_words

end AspisR1.ExtractedMaskTowerBasis
