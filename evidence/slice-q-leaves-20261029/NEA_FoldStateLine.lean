import NEA_StateBind
set_option autoImplicit false
noncomputable section
namespace NEA_FoldStateLine
open Aeneas Aeneas.Std Result AspisR1 NEA_FoldModel NEA_StateLaws

theorem source (alpha : W) (values : Array W 4#usize) (inverse : Array U32 5#usize) :
    NEA_FoldStateRef.line_ref copyW core.marker.CopyU32 NEA_StateLaws.ops () alpha values inverse
        SAQ_LineSource.quarter 1073741824#u32 = NEA_StateLaws.lift (SAQ_LineSource.line alpha values inverse) := by
  rw [← NEA_FoldModel.line]
  simp only [NEA_FoldStateRef.line_ref,NEA_FoldRef.line_ref,NEA_StateLaws.ops,NEA_StateBind.bind_pair,lift_bind]
  rfl
#print axioms source
end NEA_FoldStateLine
end
