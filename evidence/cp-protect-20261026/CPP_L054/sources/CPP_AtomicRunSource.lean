import CPP_AtomicSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicRunSource
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_AtomicSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem result {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (before : Store) (schedule : Schedule A B) :
    (eval H (program n1 copy allocator id c hashv before schedule)).2 =
      run n1 n2 copy allocator id H before schedule := by
  induction schedule generalizing before with
  | done value => rfl
  | inspect k ih => exact ih before before
  | ask query k ih => exact ih (H query) before
  | transaction code k ih =>
    simp only [program,eval_bind,eval]
    rw [CPP_AtomicSource.native c hashv n1 copy allocator id before code n2 extraction sha256 H p1 syscall,ih]
    rfl

#print axioms result
end AspisR1.CPP_AtomicRunSource
end
