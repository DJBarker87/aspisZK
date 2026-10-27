import FJs_GlobalOwners
import ARW_Nonvacuity
import ARX_AdmittedRuntime
import ART_Carrier
import ARW_AdmittedSupport
import ARW_Carrier
import ARU_OriginalSupport
import JFx_NativeBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

/-- Conditional on the STILL missing complete JFm/JFn/JFr/JFs/JFu/JFv real-byte
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
      (eval H (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = some run ∧
      run.2.2 = true ∧
      run.2.1.stored = MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes ∧
      run.2.1.physical.bytes = MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes := by
  obtain ⟨nH⟩ := (ARW_AdmittedSupport.original L copy allocator c err r native1 native2 hashv extraction a native H n syscall consistent).1
  rw [ARX_AdmittedRuntime.on_admitted L copy allocator c err r native1 native2 hashv a extraction H nH]
  exact ARW_Nonvacuity.conditional L copy allocator c err r native1 native2 hashv a extraction native H n syscall consistent realBytes

theorem owners {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    FIp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries ↔
    FJs_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries :=
  ⟨FJs_GlobalOwners.of_original _ _,FJs_GlobalOwners.complete err c r⟩

#print axioms owners

#print axioms conditional
end AspisR1.FJs_Nonvacuity
end
