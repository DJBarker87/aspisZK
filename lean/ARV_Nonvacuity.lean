import ARV_FilterOriginal
import ARV_FilterCheckpoint
import ARU_OriginalSupport
import JFx_NativeBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

/-- Conditional on the STILL missing complete JFm/JFn/JFr/JFs real-byte
accepted extracted native pair and its joint retained runtime/game tuple.
This does not construct that pair or assert it is inhabited. -/
theorem conditional
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (native H : Bytes → State)
    (n : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (consistent : ARS_AccountReplay.Consistent
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H)
    (realBytes : (eval native (submission a)).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission)) :
    ∃ run : F3T_Experiment.RunView,
      (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = some run ∧
      run.2.2 = true ∧
      run.2.1.stored = MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes ∧
      run.2.1.physical.bytes = MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes := by
  obtain ⟨original⟩ := ARU_OriginalSupport.original L copy allocator c err r native1 native2 hashv extraction a native n syscall
  have accepted := (ARU_PartialAccepted.accepted L copy allocator c err r native1 native2 hashv extraction a native original).1
  let v := eval native (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
  let run : F3T_Experiment.RunView := (v.1,(F3T_Canon.canonInput (F3T_ByteCarrier.input
    (FIp_Install.configuration err c r) (submitted v.2.1)),SCE_Experiment.accepted v.2))
  have observed : (eval native (ART_Runtime.runtime (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).2 = some run := by
    rw [ART_Runtime.eval_runtime]
  have projection := ART_Carrier.projection (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a native run observed
  rw [realBytes] at projection
  refine ⟨run,?_,accepted,projection.1,projection.2⟩
  rw [ARV_FilterOriginal.preserved L copy allocator c err r native1 native2 hashv a extraction native H n syscall consistent]
  exact observed

#print axioms conditional
end AspisR1.ARV_Nonvacuity
end
