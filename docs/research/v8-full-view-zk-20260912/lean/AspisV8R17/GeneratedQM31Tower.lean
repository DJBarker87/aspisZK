import AspisV8R17.GeneratedQM31Linear
import AspisV8R17.QM31WordTower

/-! Composition of the authenticated generated Result graphs with the actual
quadratic tower decoder. This proves source-projected arithmetic, not the
whole extraction pipeline, caller canonicality or protocol security. -/
namespace AspisV8R17.GeneratedQM31Tower
open Aeneas.Std V7Tag73CurrentHelpersOpaque GeneratedQM31Scalar

def decode (x : aspis_core.field.QM31) : QM31WordTower.Q :=
  QM31WordTower.decodeQ (GeneratedQM31Products.qmWords x)

theorem mul_correct (x y : aspis_core.field.QM31)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.QM31.mul x y = .ok z ∧ Canonical z ∧
      decode z = decode x * decode y := by
  obtain ⟨z, ez, cz, vz⟩ := GeneratedQM31Products.generated_mul_words x y hx hy
  refine ⟨z, ez, cz, ?_⟩
  unfold decode
  rw [vz, QM31WordTower.decode_mul]

theorem square_correct (x : aspis_core.field.QM31) (hx : Canonical x) :
    ∃ z, aspis_core.field.QM31.square x = .ok z ∧ Canonical z ∧
      decode z = decode x * decode x := by
  obtain ⟨z, ez, cz, vz⟩ := GeneratedQM31Products.generated_square_words x hx
  refine ⟨z, ez, cz, ?_⟩
  unfold decode
  rw [vz, QM31WordTower.decode_square]

theorem add_correct (x y : aspis_core.field.QM31)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.QM31.add x y = .ok z ∧ Canonical z ∧
      decode z = decode x + decode y := by
  obtain ⟨z, ez, cz, vz⟩ := GeneratedQM31Linear.generated_add_words x y hx hy
  refine ⟨z, ez, cz, ?_⟩
  unfold decode
  rw [vz, QM31WordTower.decode_add]

theorem sub_correct (x y : aspis_core.field.QM31)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.QM31.sub x y = .ok z ∧ Canonical z ∧
      decode z = decode x - decode y := by
  obtain ⟨z, ez, cz, vz⟩ := GeneratedQM31Linear.generated_sub_words x y hx hy
  refine ⟨z, ez, cz, ?_⟩
  unfold decode
  rw [vz]
  exact QM31WordTower.decode_sub (GeneratedQM31Products.qmWords x)
    (GeneratedQM31Products.qmWords y) hy

def decodeScalar (s : aspis_core.field.M31) : QM31WordTower.Q :=
  ⟨⟨(s.val : QM31WordTower.M),0⟩,0⟩

theorem scalar_correct (x : aspis_core.field.QM31) (s : aspis_core.field.M31) :
    ∃ z, aspis_core.field.QM31.mul_m31 x s = .ok z ∧ Canonical z ∧
      decode z = decode x * decodeScalar s := by
  obtain ⟨z, ez, cz, v0, v1, v2, v3⟩ := qm31_scalar_words x s
  refine ⟨z, ez, cz, ?_⟩
  ext <;> simp [decode, decodeScalar, QM31WordTower.decodeQ,
    QM31WordTower.embedQ, QM31WordTower.embedC, QM31WordResidues.decodeQ,
    QM31WordResidues.decodeC, GeneratedQM31Products.qmWords,
    GeneratedQM31Products.words, v0, v1, v2, v3]

#print axioms scalar_correct
#print axioms mul_correct
#print axioms square_correct
#print axioms add_correct
#print axioms sub_correct
end AspisV8R17.GeneratedQM31Tower
