import ExtractedMaskScalarMul
import ExtractedMaskQM31Exact

/-! Exact-tower scalar view for the current extracted QM31 scalar operation.
The scalar embedding is the explicit base-field element in the real-real
coordinate; the only operation fact imported is the proved current word
coordinate theorem. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskScalarExact

abbrev QM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev M31 := AspisR1.ExtractedMaskScalarMul.M31
abbrev QM31Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev M31Exact := AspisR1.ExtractedMaskQM31Exact.M31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskScalarMul.CanonicalQM

def scalarEmbedding (s : M31) : QM31Exact :=
  ⟨⟨(s.val : M31Exact), (0 : M31Exact)⟩,
    ⟨(0 : M31Exact), (0 : M31Exact)⟩⟩

private def componentWords (c : AspisR1.ExtractedMaskScalarMul.CM) : Nat × Nat :=
  (c.a.val, c.b.val)

private def qmWords (q : QM) : (Nat × Nat) × (Nat × Nat) :=
  (componentWords q.c0, componentWords q.c1)

theorem current_qm_mul_m31_exact (x : QM) (s : M31) :
    ∃ z : QM,
      AspisR1SelectedMaskProbe.field.QM31.mul_m31 x s = .ok z ∧
      CanonicalQM z ∧
      AspisR1.ExtractedMaskQM31Exact.decode z =
        AspisR1.ExtractedMaskQM31Exact.decode x * scalarEmbedding s := by
  obtain ⟨z, hz, hcanon, v0, v1, v2, v3⟩ :=
    AspisR1.ExtractedMaskScalarMul.current_qm_mul_m31_mod x s
  refine ⟨z, hz, hcanon, ?_⟩
  ext <;> simp [AspisR1.ExtractedMaskQM31Exact.decode,
    AspisR1.ExtractedMaskScalarExact.scalarEmbedding,
    AspisV8R15.ExactTowerBase.QM31Exact,
    AspisV8R15.ExactTowerBase.CM31Exact,
    v0, v1, v2, v3]

#print axioms scalarEmbedding
#print axioms current_qm_mul_m31_exact

end AspisR1.ExtractedMaskScalarExact
