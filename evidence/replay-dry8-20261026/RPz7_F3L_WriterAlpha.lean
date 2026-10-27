import RPz7_F3L_SourcePrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterAlpha
open AspisR1PublicPreparation
open F3K_CheckpointPreparedFields

theorem alpha (out : verifier.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22 := (writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out) a size qb)) :
    (CheckpointBytesBlocks.prepared (CheckpointBytesBody.fields (writerPrepared out) a size qb) canonical).alpha=
      (F3L_SourcePrepared.numeric out).alpha := by
  funext j
  have index : (writerPrepared out).alpha.val[j.val]'(by have h : (writerPrepared out).alpha.val.length=2 := (writerPrepared out).alpha.property;omega)=
      F3L_WriterSourceScalar.rawE (F3L_SourcePrepared.alpha out j) := by
    simp only [writerPrepared,CheckpointBytes3Namespaces.toPrepared,CheckpointBytes3Namespaces.mapArray,
      Tx1Q_Carriers.prepared,Tx1Q_Carriers.arr,AspisR1CurrentCaller.InstalledPreparation.currentPrepared,
      AspisR1ClaimPreparedBridge.mapArray,List.getElem_map,F3L_WriterSourceScalar.rawE,F3L_SourcePrepared.alpha]
  have cj : OraclePortCkptAbi4Decode.CanonicalWide
      (F3L_WriterSourceScalar.rawE (F3L_SourcePrepared.alpha out j)) := by
    rw [← index]
    exact canonical.alpha j
  have meaning := F3L_WriterSourceScalar.exact_e (F3L_SourcePrepared.alpha out j) cj
  simpa only [CheckpointBytesBlocks.prepared,CheckpointBytesBody.fields,index,F3L_SourcePrepared.numeric] using meaning

#print axioms alpha
end AspisR1.F3L_WriterAlpha
end
