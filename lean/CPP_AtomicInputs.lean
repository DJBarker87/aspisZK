import CPP_AtomicAuthenticated
import CPP_AtomicLifetime
import CPP_AtomicSelected
import CPP_AtomicBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicInputs
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_AtomicSchedule Hir_ProvenanceModel Hir_WriterSelect Hir_LifetimeExperiment
open S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (initial : Store) (schedule : Schedule A (Call A)) (count2 : Nat) (Q0 Q1 : Nat)
    (scheduledBound : ∀ H, (eval H (CPP_AtomicSchedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ Q0+Q1+1018)
    (genesis : ∀ key, (initial key).owner = id → ¬ Initialized (initial key).data)
    (allowed : CPP_AtomicSchedule.admissible native1 native2 copy allocator id H initial schedule)
    (post2 : Heap (Nat → Record)) (final2 : A)
    (accepted2 : let out := run native1 native2 copy allocator id H initial schedule
      CPP_Invocation.second native2 allocator id out.1 ⟨out.2.2,count2⟩ = ok (.Ok (post2,final2)))
    (project : Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    let out := run native1 native2 copy allocator id H initial schedule
    ∃ writer f s v,
      search native1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data (sites native1 native2 copy allocator id H initial schedule) = some writer ∧
      SourceCuts (DrvC_Installation.sdk c) (load writer.site.before writer.site.call.layout).first
        ((load out.1 out.2.2.layout).second secondSizes) writer.saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 (DrvC_Installation.sdk c) id
        ((load out.1 out.2.2.layout).second secondSizes) out.2.2.data out.2.2.slot = ok (.Ok v) ∧
      (DrvC_Installation.sdk c).op22 v.statement = ok (.Ok s.encoded) ∧
      select c native1 copy allocator id (eval H (CPP_AtomicLifetime.program c hashv native1 copy allocator id initial schedule)).2 =
        Hist_PairExperiment.select ⟨f,s⟩ ∧
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (CPP_AtomicJoint.program c hashv native1 copy allocator id initial schedule project)) ∨
        (bytesOf s.proof.val = bytesOf f.proof.val ∧ bytesOf s.pub.val = bytesOf f.pub.val ∧
          bytesOf s.checkpoint.val = bytesOf writer.saved.val ∧ writer.saved.val.length = 1768)) := by
  let out := run native1 native2 copy allocator id H initial schedule
  obtain ⟨count,writer,found,member,birth,accepted1,native2Accepted⟩ := CPP_AtomicSelected.selected c law native1 native2 hashv extraction
    copy allocator id sha256 H p1 syscall initial schedule count2 genesis allowed post2 final2 accepted2
  have selected : Hir_LifetimeExperiment.pairOf native1 copy allocator id
      (eval H (CPP_AtomicLifetime.program c hashv native1 copy allocator id initial schedule)).2 =
        some (Hir_FirstChoice.input writer.site.before writer.site.call,.ok (.Ok (writer.saved,writer.post,writer.final)),
          some (Hir_Choice.input out.1 out.2.2,.ok (.Ok (post2,final2)))) := by
    rw [CPP_AtomicLifetime.result c hashv native1 copy allocator id native2 extraction sha256 H p1 syscall]
    simp only [Hir_LifetimeExperiment.pairOf,found,native2Accepted]
    rfl
  obtain ⟨f,s,v,cuts,semantic,validation,encoding⟩ := Hir_BirthCuts.source c native1 native2 hashv extraction copy std allocator id
    writer.site out.1 out.2.2 writer.saved writer.post post2 writer.final final2 accepted1 native2Accepted
  have association := Hir_SelectAssociation.source c native1 copy allocator id _ writer out.1 out.2.2
    (.ok (.Ok (post2,final2))) selected f s v cuts validation encoding
  refine ⟨writer,f,s,v,found,cuts,semantic,validation,encoding,association,?_⟩
  rcases CPP_AtomicBinding.binding_or_collision c hashv native1 copy allocator id initial schedule Q0 Q1 scheduledBound project H with bad | good
  · exact Or.inl bad
  · right
    rw [association] at good
    exact CPP_AtomicAuthenticated.on_cuts c law native1 native2 hashv extraction copy std allocator id sha256 H p1 syscall
      initial schedule writer found f s cuts ⟨good⟩

#print axioms accepted
end AspisR1.CPP_AtomicInputs
end
