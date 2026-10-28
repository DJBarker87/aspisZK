import NDO_JHe_WriterHeader
import NDO_JHn_Ranges
set_option autoImplicit false
namespace AspisR1.JHn_AuthRanges
open Aeneas Aeneas.Std
attribute [local irreducible] JFx_NativeBytes.checkpoint JFx_NativeBytes.checkpointBytes
/-- The previously uncounted80 bytes are three existing adjacent ranges. -/
theorem source :
    WAdm_FissionedContent.header ++ JFq_AuthBytes.proofHash.val ++ JFq_AuthBytes.publicHash.val =
      JFx_NativeBytes.checkpoint.val.take 80 := by
  have h : WAdm_FissionedContent.header=(JFx_NativeBytes.checkpoint.val.drop 0).take 16 :=
    JFq_AuthBytes.first16.symm
  rw [h,←JFq_AuthBytes.proofHash_selected,←JFq_AuthBytes.publicHash_selected]
  change (JFx_NativeBytes.checkpoint.val.drop 0).take 16 ++
    (JFx_NativeBytes.checkpoint.val.drop 16).take 32 ++
    (JFx_NativeBytes.checkpoint.val.drop 48).take 32 = _
  rw [JHn_Ranges.adjacent _ 0 16 32,JHn_Ranges.adjacent _ 0 48 32,List.drop_zero]
#print axioms source
end AspisR1.JHn_AuthRanges
