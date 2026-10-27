import RPv_FJk_CopyDescriptor
set_option autoImplicit false
namespace AspisR1.FJk_CopyRegistry
open Aeneas Aeneas.Std FIq_Native
/-- Literal finite descriptor registry only: no field arithmetic is evaluated. -/
theorem value :
    pool_v1.pair_forest_copy_terminal.constants.COPY_LINKS.val.map FJk_CopyDescriptor.link =
      R0P.copyLinks := by
  unfold pool_v1.pair_forest_copy_terminal.constants.COPY_LINKS
  rfl
#print axioms value
end AspisR1.FJk_CopyRegistry
