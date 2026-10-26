import SCE_Execution
import GExq_WrapperAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_NativeSecond
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

theorem result (i : SecondInputs A) (post : Heap (Nat → Record)) (final : A)
    (called : second native2 allocator i.entry id i.data i.slot i.state = ok (.Ok (post,final))) :
    (eval H (secondCode c hashv allocator id i)).2 = ok (.Ok (post,final)) := by
  exact congrArg Prod.snd (GExq_WrapperAccepted.second c.adapter c.currentBase c.stageBase
    c.finish c.reserved c.query c.geometry c.boundaries c.std hashv allocator
    i.entry id i.data i.slot i.state native1 native2 extraction sha256 H p1 syscall post final called)

#print axioms result
end AspisR1.SCE_NativeSecond
end
