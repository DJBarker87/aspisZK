import F3V_EvidenceCalls
import F3V_WriterCall
import F3Q_FirstBatch
import F3Q_SecondBatch
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldBatches
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem first {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (p : OraclePortCompactDraft.Parsed) (parser : OraclePortCompactDraft.parse (bytesOf e.proof.val)=some p)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
    (q : Fin 22 → Fin 262144)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data q rho) :
    SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
      (SdkC_BatchSource.currentCode (F3U_Oracle.hashv H) e.proof e.run.p e.run.root) []).2=
      (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1 ∧
      (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2=true := by
  exact F3Q_FirstBatch.indexed (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
    c.boundaries c.std (F3U_Oracle.hashv H) (D1 c H) (fun _=>rfl) H H
    (F3V_DigestCompatibility.realization H) (F3U_Oracle.syscall H)
    e.proof (F3V_EvidenceCalls.length c B s H e) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
    e.run.p _ e.run.scratch (F3V_EvidenceCalls.preparation c B s H e) e.run.root e.rootView e.rootRange e.rootCopy
    _ p parser (OraclePortCompactDraft.parse_header _ _ parser).2 data rho q prepare e.run.batch_call

theorem second {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (p : OraclePortCompactDraft.Parsed) (parser : OraclePortCompactDraft.parse (bytesOf e.proof.val)=some p)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
    (q : Fin 22 → Fin 262144)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data q rho)
    (p2 : AspisR1Stage2.verifier.Prepared) (a2 : AspisR1Stage2.verifier.Accumulator)
    (root : Array U8 32#usize) (view : Slice U8)
    (read : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops c.reserved)
      (VTop_Checkpoint.digest (D2 c H)) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p2,a2)))
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      e.proof {start:=7751#usize,«end»:=7783#usize}=ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root))
    (batch : Op5T_Install.stageBatch Port4B_Install.leaves (D2 c H) e.proof p2 root 1#usize ()=ok (.Ok ())) :
    SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
      (SdkC_BatchSource.stageCode (F3U_Oracle.hashv H) e.proof p2 root) []).2=
      (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1 ∧
      (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).2=true := by
  rw [←F3V_DigestCompatibility.same c H] at read batch
  have len := F3V_EvidenceCalls.length c B s H e
  have wire := (OraclePortCompactDraft.parse_header _ _ parser).2
  exact F3Q_SecondBatch.indexed (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
    c.boundaries c.std (F3U_Oracle.hashv H) (D1 c H) (fun _=>rfl) H H
    (F3V_DigestCompatibility.realization H) (F3U_Oracle.syscall H)
    e.proof e.proof e.pub e.pub e.saved.deref len len e.saved c.reserved
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.run.p p2
    (Tx1Q_Carriers.accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) a2
    _ e.run.scratch (F3V_EvidenceCalls.preparation c B s H e) root view range copy _ p parser wire wire
    data rho q prepare (F3V_WriterCall.same c B s H e) rfl read batch

#print axioms first
#print axioms second
end AspisR1.PFin_WorldBatches
end
