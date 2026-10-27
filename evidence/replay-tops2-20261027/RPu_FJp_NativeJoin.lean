import RPu_FJp_Finish
import RPu_FJp_NativePair
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_NativeJoin
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
open AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Original native operands; the powers call is retained by NativeBuilder.
Recovery remains a local branch result, never an owner field. -/
theorem value {C Hash : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run
      (Tx1Q_Execution.actual ops (FIp_Install.configuration err seed r).reserved
        (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry B std)
      (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
      (FIp_Install.configuration err seed r).geometry D hash pub publicBytes proof split saved)
    (checkpoint proof1 pub1 : Slice U8) (t : Cons_Native.Witness)
    (aux : Cons_NativeBuild.Aux (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      (Tx1Q_Install.digest D) hash pub1 proof1 checkpoint t)
    (powersCall : Tx2N_Powers.powers 29#usize t.p2.gamma=ok t.g2)
    (sameSaved : MultiproofConeCanonical.bytesOf checkpoint.val=MultiproofConeCanonical.bytesOf saved.val)
    (sameProof : MultiproofConeCanonical.bytesOf proof1.val=MultiproofConeCanonical.bytesOf proof.val)
    (size : proof.val.length=57607)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (parsed : OraclePortCompactDraft.Parsed) (view : LiteralOpeningView.View)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (same : currentPrepared out=run.p)
    (numeric : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context parsed data view) data.data (SelectedChallengeMap.rhoOf data.rho) q)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data.data q (SelectedChallengeMap.rhoOf data.rho))
    (read : LiteralMatchingData.read (OraclePortStoredDecisionDraftC4.typedRows parsed q tr)=some data.data)
    (queries : OraclePortSelectedDraft.queries tr=some q)
    (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
    (H : Bytes → State) (trace : List (Bytes × State))
    (context : OraclePortCheckpointResumeC5.Context)
    (authentication : AuS1_Finish.Collision H trace parsed q ∨
      ∃ recovered : Nat → Option Bytes,∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (old : FIs_Finish.Outcome (FIp_Install.configuration err seed r).finish t.v2 t.p2
      {t.returned2 with weights:=t.back2 t.flushed2} proof1 saved H
      (MultiproofConeCanonical.bytesOf proof.val) (MultiproofConeCanonical.bytesOf publicBytes.val)
      run.p parsed trace parsed.semantic q tr data context) :
    FJp_Finish.Outcome (FIp_Install.configuration err seed r).finish t.v2 t.p2
      {t.returned2 with weights:=t.back2 t.flushed2} proof1 saved H
      (MultiproofConeCanonical.bytesOf proof.val) (MultiproofConeCanonical.bytesOf publicBytes.val)
      run.p parsed trace parsed.semantic q tr data context := by
  apply FJp_Finish.strengthen (old := old)
  rcases authentication with hit | ⟨recovered,authenticated⟩
  · exact Or.inl hit
  · right
    exact FJp_NativePair.value err seed r ops B std D hash pub publicBytes proof split saved run
      checkpoint proof1 pub1 t aux powersCall sameSaved sameProof size out parsed view q tr data
      same numeric prepare read queries wire recovered authenticated
#print axioms value
end AspisR1.FJp_NativeJoin
end
