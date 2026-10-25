import Hir_Call
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_CallSource
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers GExq_AccountExperiment Hir_Call
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

theorem first_result (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (store : Store) (call : Call A) :
    (eval H (Hir_PartialOracle.program hashv (firstCode c hashv copy allocator id store call))).2 =
      first native1 copy allocator (load store call.layout) id call.data call.state := by
  rw [(Hir_PartialOracle.exact hashv sha256 H p1 syscall _ []).1,SdkC_Source.erasure]
  exact GExq_InstalledWrapper.first_source c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std hashv copy allocator _ id call.data call.state
    native1 native2 extraction

theorem second_result (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (store : Store) (call : Call A) :
    (eval H (Hir_PartialOracle.program hashv (secondCode c hashv allocator id store call))).2 =
      second native2 allocator (load store call.layout) id call.data call.slot call.state := by
  rw [(Hir_PartialOracle.exact hashv sha256 H p1 syscall _ []).1,SdkC_Source.erasure]
  exact GExq_InstalledWrapper.second_source c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std hashv allocator _ id call.data call.slot call.state
    native1 native2 extraction

/-- Every actual selected reply, not just an accepted child, determines the
SAME computed ledger effect as the complete native wrapper. -/
theorem effect (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (store : Store) (call : Call A) :
    (eval H (oracle c hashv copy allocator id store call)).2 =
      native native1 native2 copy allocator id store call := by
  unfold oracle native
  cases route : Hiq_ReleaseRoute.route call.data with
  | first =>
    simp only [eval_bind,eval]
    rw [first_result c hashv copy allocator id native1 native2 extraction sha256 H p1 syscall]
  | second =>
    simp only [eval_bind,eval]
    rw [second_result c hashv allocator id native1 native2 extraction sha256 H p1 syscall]
  | reject => rfl

#print axioms first_result
#print axioms second_result
#print axioms effect
end AspisR1.Hir_CallSource
end
