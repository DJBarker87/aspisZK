import R1Z.PV_Inv_Circle
import Mathlib.Algebra.Field.Subfield.Basic
set_option autoImplicit false
namespace R1Z.PV_Inv_CircleSubfield
variable {K : Type} [Field K]

theorem outside_subfield_safe (S : Subfield K) (i t : K) (hi : i^2 = -1)
    (contained : i ∈ S) (outside : t ∉ S) : 1+t^2 ≠ 0 := by
  apply PV_Inv_Circle.denominator_nonzero t i hi
  · intro he
    exact outside (he ▸ contained)
  · intro he
    apply outside
    rw [he]
    exact S.neg_mem contained

#print axioms outside_subfield_safe
end R1Z.PV_Inv_CircleSubfield
