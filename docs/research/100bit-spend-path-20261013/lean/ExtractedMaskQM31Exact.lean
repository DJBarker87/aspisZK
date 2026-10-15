import ExtractedMaskQM31Tower
import AspisV8R15.ExactTowerBase

/-!
Exact-tower view of the current extracted QM31 coordinates. This adapts the
already-proved current-operation adapter to the retained exact quadratic tower;
it does not add source-correspondence claims.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskQM31Exact

abbrev CurrentQM := AspisR1.ExtractedMaskQM31Tower.CurrentQM
abbrev CurrentCanonicalQM := AspisR1.ExtractedMaskQM31Tower.CurrentCanonicalQM
abbrev M31Exact := AspisV8R15.ExactTowerBase.M31Exact
abbrev QM31Exact := AspisV8R15.ExactTowerBase.QM31Exact

def decode (x : CurrentQM) : QM31Exact :=
  ⟨⟨(x.c0.a.val : M31Exact), (x.c0.b.val : M31Exact)⟩,
    ⟨(x.c1.a.val : M31Exact), (x.c1.b.val : M31Exact)⟩⟩

theorem decode_eq_wordTower (x : CurrentQM) :
    decode x = AspisR1.ExtractedMaskQM31Tower.decode x := rfl

theorem current_qm_add_exact
    (x y : CurrentQM)
    (hx : CurrentCanonicalQM x) (hy : CurrentCanonicalQM y) :
    ∃ z : CurrentQM,
      AspisR1SelectedMaskProbe.field.QM31.add x y = .ok z ∧
      CurrentCanonicalQM z ∧ decode z = decode x + decode y := by
  obtain ⟨z, hz, hcanon, hdecode⟩ :=
    AspisR1.ExtractedMaskQM31Tower.current_qm_add_exact x y hx hy
  refine ⟨z, hz, hcanon, ?_⟩
  exact hdecode

theorem current_qm_mul_exact
    (x y : CurrentQM)
    (hx : CurrentCanonicalQM x) (hy : CurrentCanonicalQM y) :
    ∃ z : CurrentQM,
      AspisR1SelectedMaskProbe.field.QM31.mul x y = .ok z ∧
      CurrentCanonicalQM z ∧ decode z = decode x * decode y := by
  obtain ⟨z, hz, hcanon, hdecode⟩ :=
    AspisR1.ExtractedMaskQM31Tower.current_qm_mul_exact x y hx hy
  refine ⟨z, hz, hcanon, ?_⟩
  exact hdecode

#print axioms decode_eq_wordTower
#print axioms current_qm_add_exact
#print axioms current_qm_mul_exact

end AspisR1.ExtractedMaskQM31Exact
