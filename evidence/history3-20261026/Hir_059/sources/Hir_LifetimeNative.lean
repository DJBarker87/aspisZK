import Hir_LifetimeJoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_LifetimeNative
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect Hir_LifetimeExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem result {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (initial : Store) (schedule : Schedule A (Call A)) :
    (eval H (Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule)).2 =
      let out := run native1 native2 copy allocator id H initial schedule
      ((out,calls native1 native2 copy allocator id H initial schedule),
        second native2 allocator (load out.1 out.2.2.layout) id out.2.2.data out.2.2.slot out.2.2.state) := by
  simp only [Hir_LifetimeExperiment.program,eval_bind,eval]
  rw [Hir_RecordNative.result c hashv native1 native2 copy allocator id extraction sha256 H p1 syscall]
  rw [Hir_CallSource.second_result c hashv allocator id native1 native2 extraction sha256 H p1 syscall]

#print axioms result
end AspisR1.Hir_LifetimeNative
end
