import FJo_InverseCoordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_GeometryInverses
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisWide.FinalEncoder
abbrev E := AspisWideTower.WideExact
/-- Actual two inverse reads in the exact stored first-fold domain. -/
theorem value (queries : Array U32 22#usize) (start stop : Usize)
    (geo : verifier.QueryGeometry) (binding : Port5Q1_GeometryBinding.Binding queries start stop geo)
    (i : Usize) (lo : start.val ≤ i.val) (hi : i.val < stop.val)
    (inverse : Array U32 5#usize) (z : U32)
    (read : Port5Q1_GeometryBinding.forQuery geo i=ok inverse)
    (zr : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
      geo.line_z (Usize.wrapping_sub i geo.start)=ok z)
    (u : Fin 262144) (raw : (Port5Q1_GeometryBinding.queryAt queries i.val).val=u.val) :
    algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 0))=(exactCircleX u)⁻¹ ∧
    algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 1))=(exactCircleY u)⁻¹ := by
  have h := Port5Q1_GeometryAccessor.reads queries start stop geo binding i lo hi inverse z read zr
  have x := h.2 (0:Fin 5)
  have y := h.2 (1:Fin 5)
  rw [raw] at x y
  constructor
  · rw [x]
    with_reducible exact FJo_InverseCoordinates.x u
  · rw [y]
    with_reducible exact FJo_InverseCoordinates.y u
#print axioms value
end AspisR1.FJo_GeometryInverses
end
