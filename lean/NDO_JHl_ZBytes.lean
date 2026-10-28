import NDO_JHl_ZPoints
import NDO_JHk_PreparedScalarBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_ZBytes
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    ((prepared p).z.val.flatMap (fun z => WAdm_SourceBody.putK z.x++WAdm_SourceBody.putK z.y)).map
      CheckpointBytes5Writer.u8=JFq_Z0.bytes++JFq_Z1.bytes++JFq_Z2.bytes++JFq_Z3.bytes := by
  have fields := JHl_PreparedSemantic.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have zs : (Tx1Q_Carriers.prepared p).z=JFo_Prepared.value.z := by
    change Tx1Q_Carriers.arr (fun z => (⟨Tx1Q_Carriers.k z.x,Tx1Q_Carriers.k z.y⟩ :
      AspisR1Stage2.aspis_core.circle.SecureCirclePoint)) p.z=_
    rw [fields.2]
    simp only [AspisR1ClaimPreparedBridge.mapArray,Tx1Q_Carriers.arr,Array.make,
      List.map_cons,List.map_nil,JHl_ZPoints.native0,JHl_ZPoints.native1]
    rfl
  change (((Tx1Q_Carriers.prepared p).z.val.map (fun z =>
    (⟨CheckpointBytes3Namespaces.toK z.x,CheckpointBytes3Namespaces.toK z.y⟩ :
      OraclePortCkptAbi2Extracted.aspis_core.circle.SecureCirclePoint))).flatMap
      (fun z => WAdm_SourceBody.putK z.x++WAdm_SourceBody.putK z.y)).map _=_
  rw [zs]
  simp only [JFo_Prepared.value,Array.make,List.map_cons,List.map_nil,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,
    JHk_PreparedScalarBytes.encodeK,List.append_assoc]
  rfl
#print axioms source
end AspisR1.JHl_ZBytes
end
