import F3N_WriterNumeric
import F3L_WriterBody
import WAdm_SourceWriter
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_WriterModel
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes3Namespaces
open F3K_CheckpointPreparedFields MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem saved {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22:=(writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out)
      (toAccumulator a) (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb))
    (next : a.next.val=10)
    (success : Port3_CheckpointInstall.writer D
      (Tx1Q_Carriers.prepared (AspisR1CurrentCaller.InstalledPreparation.currentPrepared out)) a proof pub hash=ok saved)
    (p : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (prepared : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q)
    (accumulator : CheckpointBytes5Output.accumulator a=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator) :
    saved=Tx2N_Reader.writer H (bytesOf proof.val) (bytesOf pub.val)
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
        i.data (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator := by
  rw [F3N_WriterNumeric.saved D hash H oracle out a proof pub saved size qb canonical next success,
    prepared,accumulator]

#print axioms saved
end AspisR1.F3N_WriterModel
end
