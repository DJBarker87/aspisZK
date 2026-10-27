import RPt_FJl_Observation
import RPt_FJc_ReadSlot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_QueryRaw
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- The observed query is exactly the indexed word of the SAME prepared array. -/
theorem value (queries : Array U32 22#usize) (i : Usize) (bound : i.val<22) (q : U32)
    (read : Array.index_usize queries i=ok q) :
    Port5Q1_GeometryBinding.queryAt queries i.val=q := by
  have cell := FJc_ReadSlot.slot _ _ _ read
  simp only [Port5Q1_GeometryBinding.queryAt,cell,Option.getD_some]
#print axioms value
end AspisR1.FJo_QueryRaw
end
