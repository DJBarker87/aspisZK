import FJv_Finish
import FJt_GlobalTerminal
import FJp_ConsSecond
import FJp_NativePair
import FJu_NativeLiteral
import FJs_OnRun
import FJv_DFinish
import FJt_SourceConsumer
import FIs_OnRun
import Rc5_Literal
import FIs_Finish
import FIs_Native
import FIn_FromRead
import FIn_WeightLength
import SAG_ShapeDot
import SAF_C_SAF_FinishPrepared
import SAF_C_SAF_PreparedOutcome

import Rc4_Model
import SAQ_Constructor
import SAQ_Decoder
import SAP_LiteralFields
import SAP_NumericTransport
import SAF_C_SAF_FinishPrepared
import SAP_SaveOnRun
import SAP_Attach
import SAP_FinishParsed
import SAP_InputQuery
import T2R_Ten
import Cons_Native
import SAP_Discovery
import F3P_PreparedSource
import SAP_Immutable
import SAP_SameDigest
import SAP_Rebind
import PAln_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJv_DLiteral
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
def Outcome {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (stage : VTop_Stages.Ops) {F : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo (F3M_CircleSource.install B) std)
      reserved query geo (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (authParsed : Parsed)
    (tx2 : Cons_Native.Witness) : Prop :=
    ∃ (rawModel : Rc4_Model.Input) (parsed : Parsed) (q : Fin 22 → Fin 262144)
      (metadata : TxS_Carriers.Metadata) (view : LiteralOpeningView.View),
      let model := Rc4_Model.typed rawModel
      let tr := LiteralTranscript.erasePrefix (eval H
        (F3J_SamplerRun.program model.proof 0 33 (FS.emptyPrefix model.semantic.value))).2
      let i := TxS_Carriers.source metadata (typedRows parsed q tr)
      model.physical.bytes=bytesOf f.pub.val ∧ model.stored=bytesOf f.proof.val ∧
      OraclePortStoredParserC4.parseReached model.stored tr=some parsed ∧
      OraclePortSelectedDraft.queries tr=some q ∧ input parsed q tr=some i ∧
      LiteralMatchingData.read (typedRows parsed q tr)=some i.data ∧
      LiteralOpeningView.read (typedRows parsed q tr)=some view ∧
      SAP_LiteralFields.Fields run.p i q (OraclePortAcceptedContextC6.context parsed i view) ∧
      SAP_CurrentNumeric.numeric run.p=OraclePortCheckpointResumeC5.prepared
        (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho) q ∧
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) i.data q
        (SelectedChallengeMap.rhoOf i.rho) ∧
      Port5Q2_Prepared.PreparedFields (Tx1Q_Carriers.prepared run.p) ∧
      ∃ sourcePrepared : AspisR1PublicPreparation.verifier.Prepared,
        currentPrepared sourcePrepared=run.p ∧
        F3L_SourcePrepared.numeric sourcePrepared=OraclePortCheckpointResumeC5.prepared
          (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho) q ∧
        (AuS1_Finish.Collision H trace authParsed q ∨
          (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
            {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})=
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
              (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
          Port3_CheckpointInstall.writer (Tx1Q_Install.digest
            (SdkD_PairBatches.current adapter ops stage finish reserved query geo (F3M_CircleSource.install B) std))
            (Tx1Q_Carriers.prepared run.p) (Tx1Q_Carriers.accumulator
              {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ()=ok saved ∧
          run.flushed.val.length=64 ∧ run.out.next.val=10 ∧
          saved=Tx2N_Reader.writer H (bytesOf f.proof.val) (bytesOf f.pub.val)
            (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context parsed i view)
              i.data (SelectedChallengeMap.rhoOf i.rho) q)
            (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
              (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
          FJv_DFinish.Outcome finish tx2.v2 tx2.p2
            {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
            (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace
            parsed.semantic q tr i (OraclePortAcceptedContextC6.context parsed i view)))
theorem from_cut {CoreError : Type} (missing : IDa_Deployed.Uninstalled CoreError)
    (err : CoreError) (r : NP6_StdModel.Reservation)
    (seed : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (SdkD_PairBatches.dictionary (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current (FJt_GlobalTerminal.configuration missing err r).currentBase) (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std)
      (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (SdkD_PairBatches.current (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (header : OraclePortHeader.accepts (bytesOf f.proof.val)=true)
    (H : Bytes → State)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std)
      native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonical : scan (bytesOf f.proof.val))
    (trace : List (Bytes × State)) (authParsed : Parsed)
    (sourceParsed : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some authParsed)
    (sameProof : bytesOf f.proof.val=bytesOf s.proof.val)
    (tx2 : Cons_Native.Witness)
    (ten : T2R_Ten.Outcome run H trace authParsed)
    (finishOld : SAF_C_T2R_Finish.Outcome (FJt_GlobalTerminal.configuration missing err r).finish tx2.v2 tx2.p2
      {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed trace)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives (FJt_GlobalTerminal.configuration missing err r).query)
    (geometry : Port5Q1_GeometryCanonical.SessionAPrimitives (FJt_GlobalTerminal.configuration missing err r).geometry)
    (domain : Port5Q1_Domain.SessionADomain (FJt_GlobalTerminal.configuration missing err r).geometry)
    (multiply : (FJt_GlobalTerminal.configuration missing err r).geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : (FJt_GlobalTerminal.configuration missing err r).geometry.op7=ok (1#u32)) (inverse : (FJt_GlobalTerminal.configuration missing err r).geometry.op11=Port4C_InverseExecution.inverse_owned)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (enriched : FIs_Native.Calls (AuS1_Install.base (FJt_GlobalTerminal.configuration missing err r).stageBase) (FJt_GlobalTerminal.configuration missing err r).finish (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry D hash s.pub s.proof s.checkpoint tx2)
    (sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val)
    (authentication : ∀ (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
      (rho : OraclePortCheckpointAbiC5.K) (q : Fin 22 → Fin 262144),
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data q rho →
      AuS1_Finish.Collision H trace authParsed q ∨
      ∃ recovered : Nat → Option Bytes,∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload authParsed 2 pos)) :
    Outcome (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish (FIq_Install.boundaries seed) std
      saved f s run H trace authParsed tx2 := by
  obtain ⟨model,parsed,q,i,view,physical,stored,parser,queries,found,read,opening,prepare,fields,
    out,same,equal,endpoint,ten,finishOld⟩:=FJt_SourceConsumer.from_cut (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish seed std
      accounts1 accounts2 saved f s cuts selected run header H native1 native2 hashv extraction sha256 p1 syscall w canonical
      trace authParsed sourceParsed sameProof tx2 ten finishOld
  have parserPhysical := parser
  rw [stored] at parserPhysical
  have parsedSame : parsed=authParsed := Option.some.inj
    ((OraclePortStoredParserC4.parsed _ _ _ parserPhysical).1.symm.trans sourceParsed)
  subst authParsed
  have current : SAP_CurrentNumeric.numeric run.p=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho) q := by
    rw [←same,SAP_NumericTransport.numeric]
    exact equal
  refine ⟨Rc4_Model.erase model,parsed,q,TxS_Carriers.eraseInput i,view,?_⟩
  dsimp only
  rw [Rc4_Model.typed_erase,TxS_Carriers.source_of_read _ i read]
  refine ⟨physical,stored,parser,queries,found,read,opening,SAP_LiteralFields.of_numeric run.p i q _ current,
    current,prepare,fields,out,same,equal,?_⟩
  rcases ten ports geometry domain multiply one inverse with collision | indexed
  · exact Or.inl collision
  · right
    have oracle:=F3N_SameOracle.current (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry
      (F3M_CircleSource.install (FIq_Install.boundaries seed)) std native1 native2 hashv extraction sha256 H p1 syscall
    have sourceSaved:=SAP_SaveOnRun.saved (Op5T_Concrete.current (FJt_GlobalTerminal.configuration missing err r).currentBase) (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (FIq_Install.boundaries seed) std
      _ () _ f.pub f.proof f.split saved run ports H oracle out same
    rw [equal,indexed.1] at sourceSaved
    refine ⟨indexed.1,indexed.2.1,indexed.2.2.1,indexed.2.2.2,sourceSaved,?_⟩
    have finishSaved:=SAF_C_SAP_FinishSaved.consume (FJt_GlobalTerminal.configuration missing err r).finish tx2.v2 tx2.p2
      {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p parsed trace parsed.semantic q _ i
      (OraclePortAcceptedContextC6.context parsed i view) (finishOld _) sourceSaved
    have finished:=SAF_C_SAF_FinishSaved.strengthen (old:=finishSaved) (success:=enriched.1.2.2.2.2.2.2.2.2.1)
    have savedFields:=Tx2N_Reader.saved_ten (AuS1_Install.base (FJt_GlobalTerminal.configuration missing err r).stageBase) (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query D hash s.checkpoint s.proof s.pub
      saved tx2.p2 tx2.saved2 H (bytesOf f.proof.val) (bytesOf f.pub.val)
      (OraclePortAcceptedContextC6.context parsed i view) i.data (SelectedChallengeMap.rhoOf i.rho)
      q sameSaved sourceSaved enriched.1.1
    have identities:=SAF_PreparedPairing.identities tx2.p2 tx2.saved2 parsed i view q _ savedFields.1
    have prepared:=SAF_C_SAF_FinishPrepared.strengthen (old:=finished) (identities:=identities)
    have parsedNative:=parser
    rw [stored, sameProof] at parsedNative
    have size : tx2.saved2.weights.val.length=64 := by
      rw [savedFields.1.weights]
      simp only [List.length_map,List.length_ofFn]
    have onRun:=FIs_OnRun.strengthen (AuS1_Install.base (FJt_GlobalTerminal.configuration missing err r).stageBase) (FJt_GlobalTerminal.configuration missing err r).finish (FJt_GlobalTerminal.configuration missing err r).finish (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry D hash
      s.pub s.proof s.checkpoint saved tx2 enriched.1 enriched.2.1 _ enriched.2.2
      rfl rfl rfl rfl rfl rfl size H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p parsed parsed trace q _ i _ parsedNative read prepared
    have wire : (⟨bytesOf s.proof.val,parsed.semantic⟩ : Parsed)=parsed := by
      have h:=(OraclePortCompactDraft.parse_header _ _ (OraclePortStoredParserC4.parsed _ _ _ parsedNative).1).2
      cases parsed
      simp_all
    let c := FJt_GlobalTerminal.configuration missing err r
    let base := IDa_Deployed.deployedConfiguration missing err r
    have cutsSdk : S2W_NativeConsolidation.SourceCuts (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install c.adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base c.stageBase)
          c.reserved c.query c.geometry)) c.finish)
        (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
        (F3M_CircleSource.install (FIq_Install.boundaries seed)) std) accounts1 accounts2 saved f s := by
      rw [←AuS1_Install.dictionary]
      exact cuts
    obtain ⟨actual,actualCalls,aux⟩ := FJp_ConsSecond.accepted c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std
      accounts1 accounts2 saved f s cutsSdk
    have sizeProof : f.proof.val.length=57607 := by
      simpa only [bytesOf,List.length_map] using cuts.proofLength
    have auth := authentication _ _ q prepare
    have matching : AuS1_Finish.Collision H trace parsed q ∨ ∀ j,MatchingSupport.match0 i.data (q j) := by
      rcases auth with hit | ⟨recovered,authenticated⟩
      · exact Or.inl hit
      · right
        exact FJp_NativePair.value err base r (Op5T_Concrete.current c.currentBase)
          (F3M_CircleSource.install (FIq_Install.boundaries seed)) std _ ()
          (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
          s.checkpoint s.proof s.pub actual aux actualCalls.2 sameSaved sameProof.symm sizeProof
          out parsed view q _ i same equal prepare read queries
          (OraclePortCompactDraft.parse_header _ _ sourceParsed).2 recovered authenticated
    have matched := FJp_Finish.strengthen c.finish tx2.v2 tx2.p2
      {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p parsed trace parsed.semantic q _ i _ onRun matching
    have chained := FJu_Finish.strengthen c.finish tx2.v2 tx2.p2
      {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p parsed trace parsed.semantic q _ i _ matched (by
      intro terminal selectedView claim polys opened claimRead polyRead
      rw [wire] at opened
      have first := FIr_PhysicalInitial.on_run (Op5T_Concrete.current c.currentBase)
        c.reserved c.query c.geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std _ ()
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
        parsed q _ parserPhysical selectedView claim polys opened claimRead polyRead
      have sameView := Option.some.inj (opening.symm.trans opened)
      subst selectedView
      have chain := FIr_PhysicalChain.on_run (Op5T_Concrete.current c.currentBase)
        c.reserved c.query c.geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std _ ()
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
        parsed q _ parserPhysical view claim polys opened claimRead polyRead out same i equal
        (fun j=>FIr_TranscriptRange.view H model.proof model.semantic.value parsed q view opened (15+j.val))
      exact ⟨first,chain,terminal view claim polys (by rw [wire];exact opened) claimRead polyRead⟩)
    have range : ∀ j : Fin 10,FIr_SampleRange.InBase ((view.semantic.map Prod.snd).getD (15+j.val) 0) := by
      intro j
      exact FIr_TranscriptRange.view H model.proof model.semantic.value parsed q view opening _
    have pairLaw := FJs_OnRun.law r base.finish s.proof tx2 _ enriched.2.2 rfl rfl
      parsed q _ i view parsedNative read opening _ savedFields.1 range
    have paired := FJv_Finish.discharge c.finish tx2.v2 tx2.p2
      {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} s.proof saved H
      (bytesOf f.proof.val) (bytesOf f.pub.val) run.p parsed trace parsed.semantic q _ i _ chained pairLaw
    apply FJv_DFinish.discharge (old:=paired)
    rw [wire]
    exact endpoint
#print axioms from_cut
end AspisR1.FJv_DLiteral
end
