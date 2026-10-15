import WideTower

/-! An explicit coordinate projection from the exact wide tower to its prime
field base.  The projection is only a left inverse on the embedded base;
it is not asserted to preserve field operations on arbitrary wide values. -/

set_option autoImplicit false

namespace AspisR1.ExactBaseProjection

open AspisV8R15.ExactTowerBase
open AspisWideTower

/-- The canonical prime-field embedding into the full exact tower. -/
def embed : M31Exact →+* WideExact :=
  (algebraMap QM31Exact WideExact).comp
    ((algebraMap CM31Exact QM31Exact).comp
      (algebraMap M31Exact CM31Exact))

/-- Select the three nested real coordinates. -/
def project (x : WideExact) : M31Exact := x.re.re.re

/-- On an embedded prime-field value, the coordinate projection is exact. -/
theorem project_embed (x : M31Exact) : project (embed x) = x := by
  simp [project, embed]

/-- Every point in the embedding's field range is recovered by embedding its
explicit coordinate projection. -/
theorem embed_project_of_mem_fieldRange {x : WideExact}
    (hx : x ∈ embed.fieldRange) : embed (project x) = x := by
  obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.mp hx
  simp [project_embed]

/-- Membership in the embedded base is exactly agreement with the canonical
embedding of the extracted coordinate. -/
theorem mem_fieldRange_iff_project (x : WideExact) :
    x ∈ embed.fieldRange ↔ embed (project x) = x := by
  constructor
  · exact embed_project_of_mem_fieldRange
  · intro hx
    rw [← hx]
    exact RingHom.mem_fieldRange.mpr ⟨project x, rfl⟩

#print axioms project_embed
#print axioms embed_project_of_mem_fieldRange
#print axioms mem_fieldRange_iff_project

end AspisR1.ExactBaseProjection
