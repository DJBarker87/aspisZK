module
public import AspisV8R17.QM31WordResidues
public import AspisV8R17.QuadraticTowerOperations

/-! Concrete decoding of the shared modular words into the literal tower.
No generated execution, source loop, field or privacy theorem is assumed. -/
@[expose] public section
namespace AspisV8R17.QM31WordTower
open GeneratedQM31Products GeneratedQM31Linear
abbrev M := QM31WordResidues.M
abbrev C := QuadraticTowerOperations.C M
abbrev Q := QuadraticTowerOperations.Q M
def embedC (x : QM31WordResidues.C) : C := ⟨x.1,x.2⟩
def embedQ (x : QM31WordResidues.Q) : Q := ⟨embedC x.1,embedC x.2⟩
def decodeC (x : WordPair) : C := embedC (QM31WordResidues.decodeC x)
def decodeQ (x : WordPair × WordPair) : Q := embedQ (QM31WordResidues.decodeQ x)

theorem embed_product (x y : QM31WordResidues.Q) :
    embedQ (QM31WordResidues.qMul x y) =
      QuadraticTowerOperations.qmul (embedQ x) (embedQ y) := rfl

theorem embed_square (x : QM31WordResidues.Q) :
    embedQ (QM31WordResidues.qSquare x) =
      QuadraticTowerOperations.qsquare (embedQ x) := rfl

theorem decode_mul (x y : WordPair × WordPair) :
    decodeQ (qmMulWords x y) = decodeQ x * decodeQ y := by
  unfold decodeQ
  rw [QM31WordResidues.decode_qm_mul, embed_product,
    QuadraticTowerOperations.qmul_eq]

theorem decode_square (x : WordPair × WordPair) :
    decodeQ (qmSquareWords x) = decodeQ x * decodeQ x := by
  unfold decodeQ
  rw [QM31WordResidues.decode_qm_square, embed_square,
    QuadraticTowerOperations.qsquare_eq]

theorem decode_add (x y : WordPair × WordPair) :
    decodeQ (qmAddWords x y) = decodeQ x + decodeQ y := by
  unfold decodeQ
  rw [QM31WordResidues.decode_qm_add]
  rfl

theorem decode_sub (x y : WordPair × WordPair)
    (hy : QM31WordResidues.CanonicalPair y.1 ∧ QM31WordResidues.CanonicalPair y.2) :
    decodeQ (qmSubWords x y) = decodeQ x - decodeQ y := by
  unfold decodeQ
  rw [QM31WordResidues.decode_qm_sub x y hy]
  rfl

#print axioms embed_product
#print axioms embed_square
#print axioms decode_mul
#print axioms decode_square
#print axioms decode_add
#print axioms decode_sub
end AspisV8R17.QM31WordTower
