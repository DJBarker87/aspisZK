import RPz7_F3L_WriterBody
import RPz7_F3N_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ModelBody
open Aeneas Aeneas.Std
open F3K_CheckpointPreparedFields CheckpointBytes3Namespaces

theorem body (out : AspisR1PublicPreparation.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (hp hu : Array U8 32#usize) (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22:=(writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out)
      (toAccumulator a) (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb))
    (next : a.next.val=10)
    (p : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (prepared : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q)
    (accumulator : CheckpointBytes5Output.accumulator a=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator) :
    CheckpointBytesDecodeC5.sourceBody (writerPrepared out) (toAccumulator a) hp hu=
      OraclePortCheckpointAbiC5.body
        (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
          i.data (SelectedChallengeMap.rhoOf i.rho) q)
        (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
          (SelectedChallengeMap.rhoOf i.rho) q)).accumulator
        (CheckpointBytesDigest.stateOf hp) (CheckpointBytesDigest.stateOf hu) := by
  rw [F3L_WriterBody.body out a hp hu size qb canonical next,prepared,accumulator]

#print axioms body
end AspisR1.F3N_ModelBody
end
