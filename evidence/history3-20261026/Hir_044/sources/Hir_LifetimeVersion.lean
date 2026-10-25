import Hir_BirthCuts
import Hiq_CausalVersion
import Hiq_FirstShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_LifetimeVersion
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem causal_pair {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (H : Bytes → State)
    (initial : Store) (schedule : Schedule A (Hir_Choice.Submission A))
    (genesis : ∀ key, (initial key).owner = id → ¬ Initialized (initial key).data)
    (allowed : admissible native1 native2 copy allocator id H initial schedule)
    (post2 : Heap (Nat → Record)) (final2 : A)
    (accepted2 : let out := run native1 native2 copy allocator id H initial schedule
      let chosen := out.2.2
      second native2 allocator (load out.1 chosen.layout) id chosen.data chosen.slot chosen.state = ok (.Ok (post2,final2))) :
    let out := run native1 native2 copy allocator id H initial schedule
    ∃ site saved post1 final1 f s v,
      site ∈ calls native1 native2 copy allocator id H initial schedule ∧
      first native1 copy allocator (load site.before site.call.layout) id site.call.data site.call.state =
        ok (.Ok (saved,post1,final1)) ∧
      (site.call.layout.handles 2).1 = (out.2.2.layout.handles 6).1 ∧
      SourceCuts (DrvC_Installation.sdk c) (load site.before site.call.layout).first
        ((load out.1 out.2.2.layout).second secondSizes) saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 (DrvC_Installation.sdk c) id
        ((load out.1 out.2.2.layout).second secondSizes) out.2.2.data out.2.2.slot = ok (.Ok v) ∧
      (DrvC_Installation.sdk c).op22 v.statement = ok (.Ok s.encoded) ∧
      S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload ((load site.before site.call.layout).heap.accounts 2).1) 1768)
        (bytesOf s.checkpoint.val) := by
  let out := run native1 native2 copy allocator id H initial schedule
  obtain ⟨site,member,birth⟩ := Hir_SelectedOrigin.causal_writer c law native1 native2 hashv extraction
    copy allocator id H initial schedule genesis allowed post2 final2 accepted2
  have sameKey := birth.2.1
  obtain ⟨saved,post1,final1,front,events,accepted1,dataEq,trace,history⟩ :=
    Hir_BirthSuffix.suffix (DrvC_Installation.sdk c) law native1 native2
      (fun id accounts data => (extraction.stage1 id accounts data).symm) copy std allocator
      id H initial schedule site _ _ member birth
  obtain ⟨f,s,v,cuts,semantic,validation,encoding⟩ := Hir_BirthCuts.source c native1 native2 hashv extraction
    copy std allocator id site out.1 out.2.2 saved post1 post2 final1 final2 accepted1 accepted2
  have n1 := (first_accepted native1 copy std allocator _ id site.call.data site.call.state final1 saved post1 accepted1).1
  have source1 := (extraction.stage1 id _ site.call.data).symm.trans n1
  have shape := Hiq_FirstShape.source c id _ site.call.data saved source1
  let version := Hiq_CausalVersion.version (DrvC_Installation.sdk c) law id site.before out.1
    site.call.layout out.2.2.layout site.call.data saved source1 events trace sameKey.symm shape.1 f s cuts
  have copied := Hist_CommittedPayload.copied (DrvC_Installation.sdk c) native1 native2 hashv extraction
    copy std allocator (load site.before site.call.layout) id site.call.data site.call.state final1 saved post1 accepted1 shape.2
  exact ⟨site,saved,post1,final1,f,s,v,member,accepted1,sameKey,cuts,semantic,validation,encoding,
    Hist_CommittedPayload.committed_version _ _ _ copied version⟩

#print axioms causal_pair
end AspisR1.Hir_LifetimeVersion
end
