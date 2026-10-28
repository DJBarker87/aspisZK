import NDO_JHl_SemanticBytes
import NDO_JHn_Ranges
set_option autoImplicit false
namespace AspisR1.JHn_SemanticRanges
open Aeneas Aeneas.Std
attribute [local irreducible] JFx_NativeBytes.checkpoint JFx_NativeBytes.checkpointBytes
theorem source : JFq_Sem00.bytes ++ JFq_Sem01.bytes ++ JFq_Sem02.bytes ++ JFq_Sem03.bytes ++ JFq_Sem04.bytes ++ JFq_Sem05.bytes ++ JFq_Sem06.bytes ++ JFq_Sem07.bytes ++ JFq_Sem08.bytes ++ JFq_Sem09.bytes =
    (JFx_NativeBytes.checkpoint.val.drop 408).take 160 := by
  rw [←JFq_Sem00.selected,←JFq_Sem01.selected,←JFq_Sem02.selected,←JFq_Sem03.selected,←JFq_Sem04.selected,←JFq_Sem05.selected,←JFq_Sem06.selected,←JFq_Sem07.selected,←JFq_Sem08.selected,←JFq_Sem09.selected]
  rw [JHn_Ranges.adjacent _ 408 16 16,JHn_Ranges.adjacent _ 408 32 16,JHn_Ranges.adjacent _ 408 48 16,JHn_Ranges.adjacent _ 408 64 16,JHn_Ranges.adjacent _ 408 80 16,JHn_Ranges.adjacent _ 408 96 16,JHn_Ranges.adjacent _ 408 112 16,JHn_Ranges.adjacent _ 408 128 16,JHn_Ranges.adjacent _ 408 144 16]
#print axioms source
end AspisR1.JHn_SemanticRanges
