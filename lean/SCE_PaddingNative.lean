import SCE_NativeAccepted
import SCE_NativeFirst
import SCE_NativeSecond
import SCE_AcceptedOutcome
import SCE_PaddingFirstPass
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_PaddingNative
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution GExq_AccountExperiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)

include extraction p1 syscall

/-- Retaining the actual native/extraction boundaries does not supply the
missing adaptive chronology law. This is conditional, not a crypto attack. -/
theorem incompatible
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (a : Adversary A) (address : Bytes) (rust : F3T_TwoPass.Verifier) (saved : alloc.vec.Vec U8) (post post2 : Heap (Nat → Record)) (final final2 : A)
    (called1 : let i := (eval H a.first).2
      first native1 copy allocator i.entry id i.data i.state = ok (.Ok (saved,post,final)))
    (called2 : let i := (eval H (a.second (eval H a.first).2 saved post final)).2
      second native2 allocator i.entry id i.data i.slot i.state = ok (.Ok (post2,final2))) :
    ¬ (SCC_Physical.FirstPassBinding rust
        (F3T_Canon.canon (F3T_ByteCarrier.lift c (submission a)))
        (runtime c hashv copy allocator id a) ∧
       SCC_Physical.FirstPassBinding rust
        (F3T_Canon.canon (F3T_ByteCarrier.lift c (submission (SCE_AdaptivePadding.pad a address))))
        (runtime c hashv copy allocator id (SCE_AdaptivePadding.pad a address))) := by
  exact SCE_PaddingFirstPass.not_both c hashv copy allocator id a address H saved post final
    (SCE_NativeFirst.result c hashv allocator id native1 native2 extraction sha256 H p1 syscall
      copy _ saved post final called1)
    (SCE_NativeAccepted.accepted c hashv allocator id native1 native2 extraction sha256 H p1 syscall
      copy a saved post post2 final final2 called1 called2) rust

#print axioms incompatible
end AspisR1.SCE_PaddingNative
end
