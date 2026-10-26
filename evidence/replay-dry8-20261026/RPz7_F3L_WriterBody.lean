import RPz7_F3L_WriterPreparedEq
import F3L_WriterAccumulator
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterBody
open Aeneas Aeneas.Std
open F3K_CheckpointPreparedFields CheckpointBytes3Namespaces

theorem body (out : AspisR1PublicPreparation.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (hp hu : Array U8 32#usize) (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22:=(writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out)
      (toAccumulator a) (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb))
    (next : a.next.val=10) :
    CheckpointBytesDecodeC5.sourceBody (writerPrepared out) (toAccumulator a) hp hu=
      OraclePortCheckpointAbiC5.body (F3L_SourcePrepared.numeric out) (CheckpointBytes5Output.accumulator a)
        (CheckpointBytesDigest.stateOf hp) (CheckpointBytesDigest.stateOf hu) := by
  have source := CheckpointBytesDecodeC5.source_body_c5 (writerPrepared out) (toAccumulator a) hp hu
    (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb canonical next
  rw [F3L_WriterPreparedEq.numeric,F3L_WriterAccumulator.numeric _ _ size qb canonical next] at source
  exact source

#print axioms body
end AspisR1.F3L_WriterBody
end
