import Hir_AcceptedInputs
import Hiq_CarrierIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_AcceptedDriver
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect Hir_LifetimeExperiment
open S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)).op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (initial : Store) (schedule : Schedule A (Call A)) (Q0 Q1 : Nat)
    (scheduledBound : ∀ H, (eval H (Hir_Schedule.program native1 copy allocator id (DrvC_FirstConstants.configuration c) hashv initial schedule)).1.length ≤ Q0+Q1)
    (genesis : ∀ key, (initial key).owner = id → ¬ Initialized (initial key).data)
    (allowed : admissible native1 native2 copy allocator id H initial schedule)
    (post2 : Heap (Nat → Record)) (final2 : A)
    (accepted2 : let out := run native1 native2 copy allocator id H initial schedule
      second native2 allocator (load out.1 out.2.2.layout) id out.2.2.data out.2.2.slot out.2.2.state = ok (.Ok (post2,final2)))
    (project : Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    let out := run native1 native2 copy allocator id H initial schedule
    ∃ writer f s v,
      search native1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data (calls native1 native2 copy allocator id H initial schedule) = some writer ∧
      SourceCuts (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)) (load writer.site.before writer.site.call.layout).first
        ((load out.1 out.2.2.layout).second secondSizes) writer.saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)) id
        ((load out.1 out.2.2.layout).second secondSizes) out.2.2.data out.2.2.slot = ok (.Ok v) ∧
      (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)).op22 v.statement = ok (.Ok s.encoded) ∧
      select (DrvC_FirstConstants.configuration c) native1 copy allocator id (eval H (Hir_LifetimeExperiment.program (DrvC_FirstConstants.configuration c) hashv native1 copy allocator id initial schedule)).2 =
        Hist_PairExperiment.select ⟨f,s⟩ ∧
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hir_LifetimeJoint.program (DrvC_FirstConstants.configuration c) hashv native1 copy allocator id initial schedule project)) ∨
        ∃ i : OraclePortStoredExperimentC4.Input,
          i = Hiq_CanonicalCarrier.input f.pub f.proof ∧ Port1_StoredCarrier.Carried i ∧
          i.statement.pubBytes = bytesOf f.pub.val ∧ i.stored = bytesOf f.proof.val ∧
          (eval H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) i)).2 = true ∧
          ¬ (∀ j, (eval H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) j)).2 = false)) := by
  let r := DrvC_FirstConstants.configuration c
  let out := run native1 native2 copy allocator id H initial schedule
  obtain ⟨writer,f,s,v,found,cuts,semantic,validation,encoding,association,result⟩ :=
    Hir_AcceptedInputs.accepted r law native1 native2 hashv extraction copy std allocator id sha256 H p1 syscall
      initial schedule Q0 Q1 scheduledBound genesis allowed post2 final2 accepted2 project
  refine ⟨writer,f,s,v,found,cuts,semantic,validation,encoding,association,?_⟩
  rcases result with bad | ⟨proof,pub,checkpoint,size⟩
  · exact Or.inl bad
  · right
    obtain ⟨member,birth,accepted1,dataEq⟩ := Hir_Search.sound native1 copy allocator id _ _ _ writer found
    have native := (first_accepted native1 copy std allocator _ id writer.site.call.data writer.site.call.state
      writer.final writer.saved writer.post accepted1).1
    have source := (extraction.stage1 id _ writer.site.call.data).symm.trans native
    obtain ⟨newSemantic,decoded,newcuts⟩ := DrvC_DecodeCut.same_cut r id
      (load writer.site.before writer.site.call.layout).first ((load out.1 out.2.2.layout).second secondSizes)
      writer.site.call.data writer.saved f s source cuts
    have fit := DrvC_PublicCarrier.fits f.pub (DrvC_PublicCarrier.public_length r _ _ writer.saved f s cuts)
    let i := Hiq_CanonicalCarrier.input f.pub f.proof
    have publicCarrier : i.statement.pubBytes = bytesOf f.pub.val := Hiq_CanonicalCarrier.public_bytes _ _ fit
    have proofCarrier : i.stored = bytesOf f.proof.val := rfl
    have yes := DrvC_CutAcceptance.driver_accepts c native1 native2 hashv extraction sha256 H p1 syscall
      (load writer.site.before writer.site.call.layout).first ((load out.1 out.2.2.layout).second secondSizes)
      writer.saved {f with semantic := newSemantic} s newcuts decoded proof pub checkpoint i publicCarrier proofCarrier
    refine ⟨i,rfl,Hiq_CanonicalCarrier.carried _ _,publicCarrier,proofCarrier,yes,?_⟩
    intro rejects
    have no := (rejects i).symm.trans yes
    cases no

#print axioms accepted
end AspisR1.Hir_AcceptedDriver
end
