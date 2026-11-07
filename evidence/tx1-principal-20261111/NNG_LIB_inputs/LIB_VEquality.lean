import LIB_VCarriers
set_option autoImplicit false
noncomputable section
namespace LIB_VEquality
open Aeneas Aeneas.Std LIB_VCarriers
open LIB_VScalarCarriers (toRaw toNative native_roundtrip)
open AspisR1 AspisR1PublicPreparation
theorem scalar_injective {x y : QM31} (h : toRaw x=toRaw y) : x=y := by
 apply Subtype.ext
 have same := congrArg toNative h
 simpa only [toRaw,native_roundtrip] using same
theorem qm31 (x y : QM31) :
 aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq (toRaw x) (toRaw y)=
 .ok (@decide (x=y) (qDec x y)) := by
 classical
 rw [NJG_Comparisons.qm31]
 by_cases h : x=y
 · subst y;simp
 · have raw : toRaw x≠toRaw y := fun e=>h (scalar_injective e)
   simp only [raw,h,decide_false]
theorem point (x y : Point) : FinishModel.pointEq x y=.ok (@decide (x=y) (pDec x y)) :=
 NJG_Comparisons.point x y
#print axioms scalar_injective
#print axioms qm31
#print axioms point
end LIB_VEquality
