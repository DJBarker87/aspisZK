import NEO_CellReference
set_option autoImplicit false
namespace NEO_CellCarrier
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- The native four-coordinate observation is lossless on this exact coherent
Stage2 QM31 carrier, including noncanonical field words. Padding is not a
semantic field or an assumed valid foreign reference representation. -/
theorem qm (x y : aspis_core.field.QM31)
 (same : x.c0.a=y.c0.a ∧ x.c0.b=y.c0.b ∧ x.c1.a=y.c1.a ∧ x.c1.b=y.c1.b) : x=y := by
 cases x with
 | mk x0 x1 =>
  cases y with
  | mk y0 y1 =>
   cases x0; cases x1; cases y0; cases y1
   simp_all

/-- Every actual width-bounded accumulation iteration establishes both
indexed-getter bounds. The source width comes from the same weights slice. -/
theorem caller (weights : Slice aspis_core.field.QM31) (basis : Array U32 256#usize)
 (i : Usize) (width : weights.val.length ≤ 64) (active : i.val < weights.val.length) :
 i.val < weights.val.length ∧ i.val < basis.val.length := by
 have length := basis.property
 have size : (256#usize).val=256 := by decide
 constructor
 · exact active
 · rw [length,size]
   omega

#print axioms qm
#print axioms caller
end NEO_CellCarrier
