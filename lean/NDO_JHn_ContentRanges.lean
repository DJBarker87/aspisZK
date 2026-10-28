import NDO_JHn_QueryRanges
import NDO_JHn_SemanticRanges
import NDO_JHn_ZRanges
import NDO_JHk_KnownFields
set_option autoImplicit false
namespace AspisR1.JHn_ContentRanges
open Aeneas Aeneas.Std
attribute [local irreducible] JFx_NativeBytes.checkpoint JFx_NativeBytes.checkpointBytes
theorem source : JFq_State.bytes ++ (JFq_Root0.bytes++JFq_Root1.bytes) ++
    JFq_Gamma.bytes ++ JFq_Kappa.bytes ++ (JFq_Alpha0.bytes++JFq_Alpha1.bytes) ++
    JFq_Rho.bytes ++ JHk_PreparedRemaining.queryBytes ++
    (JFq_Sem00.bytes++JFq_Sem01.bytes++JFq_Sem02.bytes++JFq_Sem03.bytes++JFq_Sem04.bytes++
      JFq_Sem05.bytes++JFq_Sem06.bytes++JFq_Sem07.bytes++JFq_Sem08.bytes++JFq_Sem09.bytes) ++
    (JFq_Z0.bytes++JFq_Z1.bytes++JFq_Z2.bytes++JFq_Z3.bytes) ++
    JFq_Claim.bytes ++ JFq_Rhs.bytes ++ JFq_Power.bytes ++
    (JFx_NativeBytes.checkpoint.val.drop 712).take 1024 =
      (JFx_NativeBytes.checkpoint.val.drop 80).take 1656 := by
  rw [←JFq_State.selected,←JFq_Root0.selected,←JFq_Root1.selected,
    ←JFq_Gamma.selected,←JFq_Kappa.selected,←JFq_Alpha0.selected,←JFq_Alpha1.selected,
    ←JFq_Rho.selected,show JHk_PreparedRemaining.queryBytes = _ from JHn_QueryRanges.source,
    JHn_SemanticRanges.source,JHn_ZRanges.source,
    ←JFq_Claim.selected,←JFq_Rhs.selected,←JFq_Power.selected]
  simp only [←List.append_assoc]
  rw [JHn_Ranges.adjacent _ 80 32 32,JHn_Ranges.adjacent _ 80 64 32,
    JHn_Ranges.adjacent _ 80 96 32,JHn_Ranges.adjacent _ 80 128 32,
    JHn_Ranges.adjacent _ 80 160 32,JHn_Ranges.adjacent _ 80 192 32,
    JHn_Ranges.adjacent _ 80 224 16,JHn_Ranges.adjacent _ 80 240 88,
    JHn_Ranges.adjacent _ 80 328 160,JHn_Ranges.adjacent _ 80 488 64,
    JHn_Ranges.adjacent _ 80 552 32,JHn_Ranges.adjacent _ 80 584 32,
    JHn_Ranges.adjacent _ 80 616 16,JHn_Ranges.adjacent _ 80 632 1024]
#print axioms source
end AspisR1.JHn_ContentRanges
