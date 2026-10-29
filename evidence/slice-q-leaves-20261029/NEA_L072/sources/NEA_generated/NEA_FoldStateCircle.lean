import NEA_StateLaws
set_option autoImplicit false
noncomputable section
namespace NEA_FoldStateCircle
open Aeneas Aeneas.Std Result AspisR1 NEA_FoldModel NEA_StateLaws

theorem source (alpha : W) (values : Array W 4#usize) (inverse : Array U32 5#usize) :
    NEA_FoldStateRef.circle_ref copyW core.marker.CopyU32 NEA_StateLaws.ops () alpha values inverse SAQ_LineSource.quarter =
      lift (FIp_CircleSource.circle alpha values inverse) := by
  rw [← NEA_FoldModel.circle]
  simp only [NEA_FoldStateRef.circle_ref,NEA_FoldRef.circle_ref,NEA_StateLaws.ops,step,lift_bind]
#print axioms source
end NEA_FoldStateCircle
end
