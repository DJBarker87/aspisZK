import F3L_SourcePrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterSemanticAlpha
open AspisR1PublicPreparation
open F3K_CheckpointPreparedFields

theorem semantic_alpha (out : verifier.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22 := (writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out) a size qb)) :
    (CheckpointBytesBlocks.prepared (CheckpointBytesBody.fields (writerPrepared out) a size qb) canonical).semanticAlpha=
      (F3L_SourcePrepared.numeric out).semanticAlpha := by
  funext j
  have index : (writerPrepared out).semantic_alpha.val[j.val]'(by have h : (writerPrepared out).semantic_alpha.val.length=10 := (writerPrepared out).semantic_alpha.property;omega)=
      F3L_WriterSourceScalar.rawK (F3L_SourcePrepared.semanticAlpha out j) := by
    simp only [writerPrepared,CheckpointBytes3Namespaces.toPrepared,CheckpointBytes3Namespaces.mapArray,
      Tx1Q_Carriers.prepared,Tx1Q_Carriers.arr,AspisR1CurrentCaller.InstalledPreparation.currentPrepared,
      AspisR1ClaimPreparedBridge.mapArray,List.getElem_map,F3L_WriterSourceScalar.rawK,F3L_SourcePrepared.semanticAlpha]
  have cj : OraclePortCkptAbi4Decode.Canonical
      (F3L_WriterSourceScalar.rawK (F3L_SourcePrepared.semanticAlpha out j)) := by
    rw [← index]
    exact canonical.semanticAlpha j
  have meaning := F3L_WriterSourceScalar.exact_k (F3L_SourcePrepared.semanticAlpha out j) cj
  simpa only [CheckpointBytesBlocks.prepared,CheckpointBytesBody.fields,index,F3L_SourcePrepared.numeric] using meaning

#print axioms semantic_alpha
end AspisR1.F3L_WriterSemanticAlpha
end
