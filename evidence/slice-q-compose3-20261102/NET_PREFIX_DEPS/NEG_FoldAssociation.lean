import NEG_FoldsTypes.Funs
set_option autoImplicit false
noncomputable section
namespace NEG_FoldAssociation
open Aeneas Aeneas.Std Result AspisR1
abbrev E := AspisR1CurrentWide.field.wide_exact.WideExact

theorem circle (alpha : E) (a : Array E 4#usize) (inverse : Array U32 5#usize) :
    NEG_FoldsTypes.circle_fold_with_inverses alpha a inverse =
      FIp_CircleSource.circle alpha a inverse := by
  unfold NEG_FoldsTypes.circle_fold_with_inverses FIp_CircleSource.circle
  simp only [NEG_FoldsTypes.QUARTER]
  rfl

theorem line (alpha : E) (a : Array E 4#usize) (inverse : Array U32 5#usize) :
    NEG_FoldsTypes.line_fold_with_inverses alpha a inverse =
      SAQ_LineSource.line alpha a inverse := by
  unfold NEG_FoldsTypes.line_fold_with_inverses SAQ_LineSource.line
  simp only [NEG_FoldsTypes.QUARTER]
  rfl

#print axioms circle
#print axioms line
end NEG_FoldAssociation
end
