import ART_NativeCoverage
import ARQ_WorldSupport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_NativeAccepted
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

theorem accepted {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native : Bytes → State)
    (n : ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a native) :
    SCE_Experiment.accepted (eval native (ART_PartialAccount.account
      (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = true := by
  have syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native :=
    ⟨fun p d returned => (n.syscall.returningValue p d returned).trans (n.p1.realization _)⟩
  have outcome := (ART_NativeCoverage.original (FIp_Install.configuration err c r) hashv copy allocator
    CPH_Program.verifier a native syscall native1 native2 extraction).1
  rw [outcome]
  unfold ARS_NativeOutcome.wrappers
  dsimp only
  rw [n.accepted1]
  dsimp only
  rw [n.accepted2]
  rfl

#print axioms accepted
end AspisR1.ART_NativeAccepted
end
