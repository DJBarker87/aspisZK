import NDO_JHl_PreparedSemantic
import NDO_JHk_PreparedScalarBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_SemanticBytes
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

theorem cell00 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value15)))).map CheckpointBytes5Writer.u8=JFq_Sem00.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell00

theorem cell01 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value16)))).map CheckpointBytes5Writer.u8=JFq_Sem01.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell01

theorem cell02 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value17)))).map CheckpointBytes5Writer.u8=JFq_Sem02.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell02

theorem cell03 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value18)))).map CheckpointBytes5Writer.u8=JFq_Sem03.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell03

theorem cell04 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value19)))).map CheckpointBytes5Writer.u8=JFq_Sem04.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell04

theorem cell05 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value20)))).map CheckpointBytes5Writer.u8=JFq_Sem05.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell05

theorem cell06 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value21)))).map CheckpointBytes5Writer.u8=JFq_Sem06.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell06

theorem cell07 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value22)))).map CheckpointBytes5Writer.u8=JFq_Sem07.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell07

theorem cell08 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value23)))).map CheckpointBytes5Writer.u8=JFq_Sem08.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell08

theorem cell09 :
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k
      (currentQ JFm_Coordinates.value24)))).map CheckpointBytes5Writer.u8=JFq_Sem09.bytes := by
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms cell09

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    ((prepared p).semantic_alpha.val.flatMap WAdm_SourceBody.putK).map CheckpointBytes5Writer.u8=
      JFq_Sem00.bytes++JFq_Sem01.bytes++JFq_Sem02.bytes++JFq_Sem03.bytes++JFq_Sem04.bytes++
      JFq_Sem05.bytes++JFq_Sem06.bytes++JFq_Sem07.bytes++JFq_Sem08.bytes++JFq_Sem09.bytes := by
  have fields := JHl_PreparedSemantic.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  change (((Tx1Q_Carriers.arr Tx1Q_Carriers.k p.semantic_alpha).val.map
    CheckpointBytes3Namespaces.toK).flatMap WAdm_SourceBody.putK).map _=_
  rw [fields.1]
  simp only [AspisR1ClaimPreparedBridge.mapArray,Tx1Q_Carriers.arr,JFm_PartialAlpha.a10,
    List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,List.append_assoc,
    cell00,    cell01,    cell02,    cell03,    cell04,    cell05,    cell06,    cell07,    cell08,    cell09]
#print axioms source
end AspisR1.JHl_SemanticBytes
end
