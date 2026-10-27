import FIs_Literal
import FJp_NativeJoin
import FJp_Native
import FJp_ConsSecond
import FJp_NativeLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_ActualLiteral
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
theorem strengthen {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (saved : alloc.vec.Vec U8) (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (run : Tx1Q_Execution.Run
      (Tx1Q_Execution.actual (Op5T_Concrete.current (FIp_Install.configuration err seed r).currentBase)
        (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
        (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) std)
      (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
      (FIp_Install.configuration err seed r).geometry
      (SdkD_PairBatches.current (FIp_Install.configuration err seed r).adapter (FIp_Install.configuration err seed r).currentBase
        (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish
        (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
        (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (authParsed : Parsed) (t : Cons_Native.Witness)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install (FIp_Install.configuration err seed r).adapter
          (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (FIp_Install.configuration err seed r).stageBase)
            (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
            (FIp_Install.configuration err seed r).geometry)) (FIp_Install.configuration err seed r).finish)
        (Uni_Install.current (FIp_Install.configuration err seed r).currentBase
          (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
          (FIp_Install.configuration err seed r).geometry) (F3M_CircleSource.install B) std)
      accounts1 accounts2 saved f s)
    (sourceParsed : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some authParsed)
    (sameProof : bytesOf s.proof.val=bytesOf f.proof.val)
    (sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val)
    (size : f.proof.val.length=57607)
    (authentication : ∀ (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
      (rho : OraclePortCheckpointAbiC5.K) (q : Fin 22 → Fin 262144),
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data q rho →
      AuS1_Finish.Collision H trace authParsed q ∨
      ∃ recovered : Nat → Option Bytes,∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload authParsed 2 pos))
    (old : FIs_Literal.Outcome (FIp_Install.configuration err seed r).adapter
      (FIp_Install.configuration err seed r).currentBase (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish
      B std saved f s run H trace authParsed t) :
    FJp_NativeLiteral.Outcome (FIp_Install.configuration err seed r).adapter
      (FIp_Install.configuration err seed r).currentBase (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish
      B std saved f s run H trace authParsed t := by
  let c := FIp_Install.configuration err seed r
  obtain ⟨actual,enriched,aux⟩ := FJp_ConsSecond.accepted c.adapter c.currentBase c.stageBase c.finish
    c.reserved c.query c.geometry (F3M_CircleSource.install B) std accounts1 accounts2 saved f s cuts
  obtain ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,remaining⟩ := old
  have parsed0 : OraclePortCompactDraft.parse (bytesOf f.proof.val)=some parsed := by
    rw [←stored]
    exact (OraclePortStoredParserC4.parsed _ _ _ parser).1
  have equal : parsed=authParsed := Option.some.inj (parsed0.symm.trans sourceParsed)
  subst authParsed
  refine ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,?_⟩
  rcases remaining with hit | good
  · exact Or.inl hit
  · right
    obtain ⟨acc,writer,len,next,savedEq,finishing⟩ := good
    refine ⟨acc,writer,len,next,savedEq,?_⟩
    have auth := authentication _ _ q prepare
    apply FJp_Finish.strengthen (old := finishing)
    rcases auth with hit | ⟨recovered,authenticated⟩
    · exact Or.inl hit
    · right
      exact FJp_NativePair.value err seed r (Op5T_Concrete.current c.currentBase)
        (F3M_CircleSource.install B) std _ () (AspisS6CurrentVerifierCarrier.toPublic f.semantic)
        f.pub f.proof f.split saved run s.checkpoint s.proof s.pub actual aux enriched.2
        sameSaved sameProof size out parsed view q _ _ output sourceNumeric prepare read queries
        (OraclePortCompactDraft.parse_header _ _ parsed0).2 recovered authenticated
#print axioms strengthen
end AspisR1.FJp_ActualLiteral
end
