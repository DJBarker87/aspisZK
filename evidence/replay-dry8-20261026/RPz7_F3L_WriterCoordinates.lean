import RPz7_F3L_SourcePrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterCoordinates
open AspisR1PublicPreparation
open F3K_CheckpointPreparedFields

theorem coordinates (out : verifier.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22 := (writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out) a size qb)) :
    (CheckpointBytesBlocks.prepared (CheckpointBytesBody.fields (writerPrepared out) a size qb) canonical).coordinates=
      (F3L_SourcePrepared.numeric out).coordinates := by
  funext j
  have index : (CheckpointBytesBody.fields (writerPrepared out) a size qb).coordinates j=
      F3L_WriterSourceScalar.rawK (F3L_SourcePrepared.coordinate out j) := by
    fin_cases j <;>
      simp only [CheckpointBytesBody.fields,writerPrepared,CheckpointBytes3Namespaces.toPrepared,
        CheckpointBytes3Namespaces.mapArray,CheckpointBytes3Namespaces.toPoint,
        Tx1Q_Carriers.prepared,Tx1Q_Carriers.arr,AspisR1CurrentCaller.InstalledPreparation.currentPrepared,
        AspisR1ClaimPreparedBridge.mapArray,List.getElem_map,F3L_WriterSourceScalar.rawK,
        F3L_SourcePrepared.coordinate,F3L_SourcePrepared.point,
        AspisR1CurrentCaller.InstalledPreparation.currentPoint] <;> rfl
  have cj : OraclePortCkptAbi4Decode.Canonical
      (F3L_WriterSourceScalar.rawK (F3L_SourcePrepared.coordinate out j)) := by
    rw [← index]
    exact canonical.coordinates j
  have meaning := F3L_WriterSourceScalar.exact_k (F3L_SourcePrepared.coordinate out j) cj
  simpa only [CheckpointBytesBlocks.prepared,index,F3L_SourcePrepared.numeric] using meaning

#print axioms coordinates
end AspisR1.F3L_WriterCoordinates
end
