import NEA_FoldStateRef.Funs
import NEA_FoldModel
import NDD_ResultLaws
set_option autoImplicit false
noncomputable section
namespace NEA_FoldStateModel
open Aeneas Aeneas.Std Result AspisR1
open NEA_FoldModel

def lift {A : Type} (r : Result A) : Result (A × Unit) := do
  let x ← r
  ok (x,())
def ops : NEA_FoldStateRef.NEA_Ops Unit W U32 where
  add := fun _ x y => lift (NEA_FoldModel.ops.add x y)
  sub := fun _ x y => lift (NEA_FoldModel.ops.sub x y)
  mul := fun _ x y => lift (NEA_FoldModel.ops.mul x y)
  scale := fun _ x y => lift (NEA_FoldModel.ops.scale x y)
  base_mul := fun _ x y => lift (NEA_FoldModel.ops.base_mul x y)

theorem circle (alpha : W) (values : Array W 4#usize) (inverse : Array U32 5#usize) :
    NEA_FoldStateRef.circle_ref copyW core.marker.CopyU32 ops () alpha values inverse SAQ_LineSource.quarter =
      lift (FIp_CircleSource.circle alpha values inverse) := by
  simp only [NEA_FoldStateRef.circle_ref,FIp_CircleSource.circle,ops,NEA_FoldModel.ops,lift,
    bind_assoc_eq,bind_tc_ok]

theorem line (alpha : W) (values : Array W 4#usize) (inverse : Array U32 5#usize) :
    NEA_FoldStateRef.line_ref copyW core.marker.CopyU32 ops () alpha values inverse
        SAQ_LineSource.quarter 1073741824#u32 = lift (SAQ_LineSource.line alpha values inverse) := by
  simp only [NEA_FoldStateRef.line_ref,SAQ_LineSource.line,ops,NEA_FoldModel.ops,lift,
    bind_assoc_eq,bind_tc_ok]
#print axioms circle
#print axioms line
end NEA_FoldStateModel
end
