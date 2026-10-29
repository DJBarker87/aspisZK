import NEA_FoldRef.Funs
import FIp_CircleQuery
set_option autoImplicit false
noncomputable section
namespace NEA_FoldModel
open Aeneas Aeneas.Std Result AspisR1
abbrev W := AspisR1CurrentWide.field.wide_exact.WideExact

def ops : NEA_FoldRef.NEA_Ops Unit W U32 where
  add := AspisR1CurrentWide.field.wide_exact.WideExact.add
  sub := AspisR1CurrentWide.field.wide_exact.WideExact.sub
  mul := AspisR1CurrentWide.field.wide_exact.WideExact.mul
  scale := AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31
  base_mul := AspisR1CurrentWide.field.M31.mul

def copyW : core.marker.Copy W := {cloneInst:={clone:=fun x=>ok x}}

theorem circle (alpha : W) (values : Array W 4#usize) (inverse : Array U32 5#usize) :
    NEA_FoldRef.circle_ref copyW core.marker.CopyU32 ops alpha values inverse SAQ_LineSource.quarter =
      FIp_CircleSource.circle alpha values inverse := by
  rfl

theorem line (alpha : W) (values : Array W 4#usize) (inverse : Array U32 5#usize) :
    NEA_FoldRef.line_ref copyW core.marker.CopyU32 ops alpha values inverse
        SAQ_LineSource.quarter 1073741824#u32 =
      SAQ_LineSource.line alpha values inverse := by
  rfl

theorem circle_cohort (alpha : SAQ_WideABI.E) (values : Array SAQ_WideABI.E 4#usize)
    (inverse : Array U32 5#usize) :
    (do let z ← NEA_FoldRef.circle_ref copyW core.marker.CopyU32 ops
          (SAQ_WideABI.toW alpha) (FIp_CircleQuery.toValues values) inverse SAQ_LineSource.quarter
        ok (SAQ_WideABI.fromW z)) = FIp_CircleQuery.circle alpha values inverse := by
  rw [circle]
  rfl

#print axioms circle
#print axioms line
#print axioms circle_cohort
end NEA_FoldModel
end
