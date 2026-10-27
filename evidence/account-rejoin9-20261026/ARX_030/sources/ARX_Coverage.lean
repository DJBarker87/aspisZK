import ARX_AdmittedRuntime
import ARW_AdmittedSupport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_Coverage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
attribute [local instance] Classical.propDecidable

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)


/-- Bank tuple, BOTH admissions, approved game and persistence are supplied
by this execution's own SupportedEntry, never by the independent root pair. -/
theorem coverage
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (native H : Bytes → State)
    (tuple : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (consistent : ARS_AccountReplay.Consistent
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    eval H (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) =
    eval native (ART_Runtime.runtime (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) := by
  obtain ⟨⟨n⟩,same⟩ := ARW_AdmittedSupport.original L copy allocator c err r native1 native2 hashv extraction a native H tuple syscall consistent
  refine ⟨⟨n⟩,?_⟩
  rw [ARX_AdmittedRuntime.on_admitted L copy allocator c err r native1 native2 hashv a extraction H n,
    ART_Runtime.eval_runtime,ART_Runtime.eval_runtime,same]
#print axioms coverage
end AspisR1.ARX_Coverage
end
