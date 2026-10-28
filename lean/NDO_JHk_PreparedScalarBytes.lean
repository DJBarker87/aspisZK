import NDO_JHe_CurrentWriterImage
import NDO_JHa_CurrentFields
import NDO_JHa_CurrentRho
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_PreparedScalarBytes
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

/-- Reuse the emitted-word layout lemma instead of reducing BitVec output. -/
theorem encodeK (q : OraclePortCkptAbi2Extracted.aspis_core.field.QM31) :
    (WAdm_SourceBody.putK q).map CheckpointBytes5Writer.u8=
      (OraclePortCompactDraft.le32 q.c0.a.val ++ OraclePortCompactDraft.le32 q.c0.b.val ++
       OraclePortCompactDraft.le32 q.c1.a.val ++ OraclePortCompactDraft.le32 q.c1.b.val).map
        CheckpointBytes5Writer.u8 := by
  have bytes : MultiproofConeCanonical.bytesOf (CheckpointP6EncodeK.bytes q)=
      OraclePortCompactDraft.le32 q.c0.a.val ++ OraclePortCompactDraft.le32 q.c0.b.val ++
      OraclePortCompactDraft.le32 q.c1.a.val ++ OraclePortCompactDraft.le32 q.c1.b.val := by
    simp only [CheckpointP6EncodeK.bytes,MultiproofConeCanonical.bytesOf,List.map_append]
    change MultiproofConeCanonical.bytesOf (core.num.U32.to_le_bytes q.c0.a).val ++
      MultiproofConeCanonical.bytesOf (core.num.U32.to_le_bytes q.c0.b).val ++
      MultiproofConeCanonical.bytesOf (core.num.U32.to_le_bytes q.c1.a).val ++
      MultiproofConeCanonical.bytesOf (core.num.U32.to_le_bytes q.c1.b).val=_
    rw [CheckpointP6KBytes.word_bytes,CheckpointP6KBytes.word_bytes,
      CheckpointP6KBytes.word_bytes,CheckpointP6KBytes.word_bytes]
  exact congrArg (List.map CheckpointBytes5Writer.u8) bytes
#print axioms encodeK

theorem rawKBytes (q : OraclePortCkptAbi2Extracted.aspis_core.field.QM31) :
    CheckpointP6EncodeK.bytes q=
      (OraclePortCompactDraft.le32 q.c0.a.val ++ OraclePortCompactDraft.le32 q.c0.b.val ++
       OraclePortCompactDraft.le32 q.c1.a.val ++ OraclePortCompactDraft.le32 q.c1.b.val).map
        CheckpointBytes5Writer.u8 := by
  have h := encodeK q
  change (MultiproofConeCanonical.bytesOf (CheckpointP6EncodeK.bytes q)).map
    CheckpointBytes5Writer.u8=_ at h
  rw [WAdm_SourceWriter.map_bytes] at h
  exact h
#print axioms rawKBytes

/-- The actual writer's early scalar fields, byte for byte. The preparation
is the actual returned preparation, not a fixture supplied as an operand. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    (WAdm_SourceBody.put (prepared p).gamma).map CheckpointBytes5Writer.u8=JFq_Gamma.bytes ∧
    (WAdm_SourceBody.put (prepared p).kappa).map CheckpointBytes5Writer.u8=JFq_Kappa.bytes ∧
    ((prepared p).alpha.val.flatMap WAdm_SourceBody.put).map CheckpointBytes5Writer.u8=
      JFq_Alpha0.bytes++JFq_Alpha1.bytes ∧
    (WAdm_SourceBody.putK (prepared p).rho).map CheckpointBytes5Writer.u8=JFq_Rho.bytes := by
  have fields := JHa_CurrentFields.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have rho := JHa_CurrentRho.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  change (WAdm_SourceBody.put (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.e p.gamma))).map _=_ ∧
    (WAdm_SourceBody.put (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.e p.kappa))).map _=_ ∧
    (((Tx1Q_Carriers.arr Tx1Q_Carriers.e p.alpha).val.map CheckpointBytes3Namespaces.toE).flatMap
      WAdm_SourceBody.put).map _=_ ∧
    (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK (Tx1Q_Carriers.k p.rho))).map _=_
  rw [fields.1,fields.2.1,fields.2.2,rho.1]
  rw [encodeK]
  simp only [WAdm_SourceBody.put,WAdm_SourceBody.putK,CheckpointBytesBlocks.rawK,
    WAdm_SourceWriter.map_bytes,CheckpointBytesE.rawBytes,rawKBytes,JFo_Prepared.value,Array.make,
    List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append]
  exact ⟨rfl,rfl,rfl,rfl⟩
#print axioms source
end AspisR1.JHk_PreparedScalarBytes
end
