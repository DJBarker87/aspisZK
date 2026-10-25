import Hir_SelectAssociation
import Hiq_LightAuthenticated
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_Authenticated
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem on_cuts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (initial : Store) (schedule : Schedule A (Call A)) (writer : Writer A)
    (found : let out := run native1 native2 copy allocator id H initial schedule
      search native1 copy allocator id (out.2.2.layout.handles 6).1
        (out.1 (out.2.2.layout.handles 6).1).data (calls native1 native2 copy allocator id H initial schedule) = some writer)
    (f : FirstCut) (s : SecondCut)
    (cuts : let out := run native1 native2 copy allocator id H initial schedule
      SourceCuts (DrvC_Installation.sdk c) (load writer.site.before writer.site.call.layout).first
        ((load out.1 out.2.2.layout).second secondSizes) writer.saved f s)
    (binding : S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub) :
    bytesOf s.proof.val = bytesOf f.proof.val ∧ bytesOf s.pub.val = bytesOf f.pub.val ∧
      bytesOf s.checkpoint.val = bytesOf writer.saved.val ∧ writer.saved.val.length = 1768 := by
  obtain ⟨version⟩ := Hir_SelectedVersion.on_cuts c law native1 native2 hashv extraction copy std allocator
    id H initial schedule writer found f s cuts
  have shape := Hiq_FirstShape.decoded c f.semantic f.pub f.proof f.split writer.saved cuts.first
  obtain ⟨member,birth,accepted1,dataEq⟩ := Hir_Search.sound native1 copy allocator id _ _ _ writer found
  have copied := Hist_CommittedPayload.copied (DrvC_Installation.sdk c) native1 native2 hashv extraction copy std allocator
    (load writer.site.before writer.site.call.layout) id writer.site.call.data writer.site.call.state
    writer.final writer.saved writer.post accepted1 shape.2
  have persisted := S2X.checkpoint_persistence _ _ version
  rw [copied] at persisted
  have oracle := S2W_DigestExtraction.native_oracle _ native1 native2 hashv extraction sha256 H p1 syscall
  have wrote := Hiq_InstalledHeader.decoded c f.semantic f.pub f.proof f.split writer.saved cuts.first H oracle
  have read := Hiq_DrvReaderHeader.header c _ _ writer.saved f s cuts H oracle
  rw [persisted,wrote] at read
  have paired := Option.some.inj read
  have matched : R9PoolRuntimeBinding.digestMatches H
      ⟨bytesOf f.proof.val,bytesOf f.pub.val⟩ ⟨bytesOf s.proof.val,bytesOf s.pub.val⟩ :=
    ⟨(congrArg Prod.fst paired).symm,(congrArg Prod.snd paired).symm⟩
  obtain ⟨proof,pub⟩ := binding.binding matched
  exact ⟨proof,pub,persisted,shape.2⟩

#print axioms on_cuts
end AspisR1.Hir_Authenticated
end
