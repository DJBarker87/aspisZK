import ExtractedMaskTowerBasis
import ExtractedMaskQM31Exact
import AspisV8R17.QM31WordResidues
import AspisV8R17.QM31WordTower
import AspisV8R17.QuadraticTowerOperations
import AspisV8R15.ExactTowerBase

/-! Decode the source-shaped tower-basis word maps into multiplication by the
literal basis elements of the retained exact quadratic tower. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskTowerBasisExact

open AspisV8R15.ExactTowerBase

abbrev P : Nat := AspisV8R15.ExactTowerBase.P
abbrev WordPair := AspisR1.ExtractedMaskQM31Mul.WordPair
abbrev WordQM := WordPair × WordPair
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev QMExact := AspisV8R15.ExactTowerBase.QM31Exact

abbrev iWords := AspisR1.ExtractedMaskTowerBasis.iWords
abbrev basisWords := AspisR1.ExtractedMaskTowerBasis.basisWords

def iCM : CMExact := ⟨0, 1⟩
def iQM : QMExact := ⟨iCM, 0⟩
def uQM : QMExact := ⟨0, 1⟩
def basisElement (coordinate : Nat) : QMExact :=
  match coordinate with
  | 0 => 1
  | 1 => iQM
  | 2 => uQM
  | 3 => iQM * uQM
  | _ => 1

def decodeC (x : WordPair) : CMExact :=
  AspisV8R17.QM31WordTower.decodeC x

def decodeQ (x : WordQM) : QMExact :=
  AspisV8R17.QM31WordTower.decodeQ x

private theorem mul_base_exact (a : CMExact) (z : QMExact) :
    (⟨a, 0⟩ : QMExact) * z = ⟨a * z.re, a * z.im⟩ := by
  apply QuadraticAlgebra.ext <;> simp

private theorem mul_u_exact (z : QMExact) :
    uQM * z = ⟨AspisV8R15.ExactTowerBase.qm31R * z.im, z.re⟩ := by
  apply QuadraticAlgebra.ext <;> simp [uQM]

private theorem decode_r_exact (x : WordPair)
    (hx : AspisV8R17.QM31WordResidues.CanonicalPair x) :
    decodeC (AspisR1.ExtractedMaskQM31Mul.rWords x) =
      AspisV8R15.ExactTowerBase.qm31R * decodeC x := by
  have hr := congrArg AspisV8R17.QM31WordTower.embedC
    (AspisV8R17.QM31WordResidues.decode_r x hx)
  have hc (z : AspisV8R17.QM31WordResidues.C) :
      AspisV8R17.QM31WordTower.embedC
          (AspisV8R17.QM31WordResidues.cR z) =
        AspisV8R17.QuadraticTowerOperations.cr
          (AspisV8R17.QM31WordTower.embedC z) := by
    ext <;> simp [AspisV8R17.QM31WordTower.embedC,
      AspisV8R17.QM31WordResidues.cR,
      AspisV8R17.QuadraticTowerOperations.cr] <;> ring
  rw [hc, AspisV8R17.QuadraticTowerOperations.cr_eq] at hr
  simpa [decodeC, AspisV8R17.QM31WordTower.decodeC,
    AspisV8R17.QM31WordTower.embedC,
    AspisV8R17.QM31WordResidues.decodeC,
    AspisV8R17.QuadraticTowerOperations.r,
    AspisV8R15.ExactTowerBase.qm31R,
    AspisR1.ExtractedMaskQM31Mul.rWords,
    AspisV8R17.GeneratedQM31Products.rWords] using hr

private theorem decode_iWords (x : WordPair)
    (hx : AspisV8R17.QM31WordResidues.CanonicalPair x) :
    decodeC (iWords x) = iCM * decodeC x := by
  rw [← AspisV8R17.QuadraticTowerOperations.cmul_eq]
  apply QuadraticAlgebra.ext
  · simp only [decodeC, AspisV8R17.QM31WordTower.decodeC,
      AspisV8R17.QM31WordTower.embedC,
      AspisV8R17.QM31WordResidues.decodeC, iWords,
      AspisR1.ExtractedMaskTowerBasis.iWords]
    simpa [P, AspisR1.ExtractedMaskTowerBasis.P,
      AspisR1.ExtractedMaskTowerAdd.P,
      AspisR1.ExtractedMaskM31AddSub.P,
      AspisV8R17.RawReducer.P,
      AspisV8R17.QuadraticTowerOperations.cmul, iCM] using
      (AspisV8R17.QM31WordResidues.sub_cast 0 x.2 hx.2)
  · simp [decodeC, AspisV8R17.QM31WordTower.decodeC,
      AspisV8R17.QM31WordTower.embedC,
      AspisV8R17.QM31WordResidues.decodeC, iWords,
      AspisR1.ExtractedMaskTowerBasis.iWords,
      AspisV8R17.QuadraticTowerOperations.cmul, iCM]

private theorem decode_iWordsQ (x : WordQM)
    (hx : AspisV8R17.QM31WordResidues.CanonicalPair x.1 ∧
      AspisV8R17.QM31WordResidues.CanonicalPair x.2) :
    decodeQ (iWords x.1, iWords x.2) = iQM * decodeQ x := by
  have h₁ := decode_iWords x.1 hx.1
  have h₂ := decode_iWords x.2 hx.2
  change (⟨decodeC (iWords x.1), decodeC (iWords x.2)⟩ : QMExact) =
    iQM * ⟨decodeC x.1, decodeC x.2⟩
  rw [h₁, h₂]
  exact (mul_base_exact iCM ⟨decodeC x.1, decodeC x.2⟩).symm

private theorem decode_uWordsQ (x : WordQM)
    (hx : AspisV8R17.QM31WordResidues.CanonicalPair x.1 ∧
      AspisV8R17.QM31WordResidues.CanonicalPair x.2) :
    decodeQ (AspisR1.ExtractedMaskQM31Mul.rWords x.2, x.1) =
      uQM * decodeQ x := by
  change (⟨decodeC (AspisR1.ExtractedMaskQM31Mul.rWords x.2),
      decodeC x.1⟩ : QMExact) =
    uQM * ⟨decodeC x.1, decodeC x.2⟩
  rw [decode_r_exact x.2 hx.2]
  exact (mul_u_exact ⟨decodeC x.1, decodeC x.2⟩).symm

theorem decode_basisWords (x : WordQM) (coordinate : Nat)
    (hcoord : coordinate < 4)
    (hx : AspisV8R17.QM31WordResidues.CanonicalPair x.1 ∧
      AspisV8R17.QM31WordResidues.CanonicalPair x.2) :
    decodeQ (basisWords x coordinate) = basisElement coordinate * decodeQ x := by
  have hcases : coordinate = 0 ∨ coordinate = 1 ∨
      coordinate = 2 ∨ coordinate = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · subst coordinate
    change decodeQ x = (1 : QMExact) * decodeQ x
    simp
  · subst coordinate
    change decodeQ (iWords x.1, iWords x.2) = iQM * decodeQ x
    exact decode_iWordsQ x hx
  · subst coordinate
    change decodeQ (AspisR1.ExtractedMaskQM31Mul.rWords x.2, x.1) =
      uQM * decodeQ x
    exact decode_uWordsQ x hx
  · subst coordinate
    have hr : AspisV8R17.QM31WordResidues.CanonicalPair
        (AspisR1.ExtractedMaskQM31Mul.rWords x.2) := by
      constructor <;> exact Nat.mod_lt _ (by norm_num [P])
    calc
      decodeQ (basisWords x 3) = iQM * decodeQ (basisWords x 2) := by
        change decodeQ (iWords (AspisR1.ExtractedMaskQM31Mul.rWords x.2),
          iWords x.1) = iQM * decodeQ
            (AspisR1.ExtractedMaskQM31Mul.rWords x.2, x.1)
        exact decode_iWordsQ
          (AspisR1.ExtractedMaskQM31Mul.rWords x.2, x.1) ⟨hr, hx.1⟩
      _ = iQM * (uQM * decodeQ x) := by
        change iQM * decodeQ
          (AspisR1.ExtractedMaskQM31Mul.rWords x.2, x.1) = _
        exact congrArg (fun y : QMExact => iQM * y) (decode_uWordsQ x hx)
      _ = basisElement 3 * decodeQ x := by
        simp [basisElement, mul_assoc]

 theorem current_mul_tower_basis_exact
    (x : AspisR1.ExtractedMaskQM31Exact.CurrentQM)
    (coordinate : Aeneas.Std.Usize)
    (hx : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM x)
    (hcoord : coordinate.val < 4) :
    ∃ z : AspisR1.ExtractedMaskQM31Exact.CurrentQM,
      AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis x coordinate = .ok z ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM z ∧
      AspisR1.ExtractedMaskQM31Exact.decode z =
        basisElement coordinate.val * AspisR1.ExtractedMaskQM31Exact.decode x := by
  obtain ⟨z, hz, hcanon, hwords⟩ :=
    AspisR1.ExtractedMaskTowerBasis.current_mul_tower_basis_words x coordinate hx hcoord
  refine ⟨z, hz, hcanon, ?_⟩
  have hxwords :
      AspisV8R17.QM31WordResidues.CanonicalPair
          (AspisR1.ExtractedMaskTowerAdd.wordsCM x.c0) ∧
        AspisV8R17.QM31WordResidues.CanonicalPair
          (AspisR1.ExtractedMaskTowerAdd.wordsCM x.c1) := hx
  calc
    AspisR1.ExtractedMaskQM31Exact.decode z = decodeQ
        (AspisR1.ExtractedMaskTowerAdd.wordsQM z) := by rfl
    _ = decodeQ (basisWords (AspisR1.ExtractedMaskTowerAdd.wordsQM x)
        coordinate.val) := by rw [hwords]
    _ = basisElement coordinate.val * decodeQ
        (AspisR1.ExtractedMaskTowerAdd.wordsQM x) :=
          decode_basisWords _ _ hcoord hxwords
    _ = basisElement coordinate.val * AspisR1.ExtractedMaskQM31Exact.decode x := by rfl

#print axioms decode_iWords
#print axioms decode_iWordsQ
#print axioms decode_uWordsQ
#print axioms decode_basisWords
#print axioms current_mul_tower_basis_exact

end AspisR1.ExtractedMaskTowerBasisExact
