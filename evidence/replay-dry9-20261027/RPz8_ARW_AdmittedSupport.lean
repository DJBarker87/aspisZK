import RPz8_ARU_OriginalFactory
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARW_AdmittedSupport
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
/-- An admitted native execution is supplied on its OWN selected entries.
The factory derives query-restricted support throughout its full cylinder.
This theorem does not obtain an adversary-indexed admission from Rc10's
independent e1/e2 admissions. -/
theorem original {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native H : Bytes → State)
    (n : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (consistent : ARS_AccountReplay.Consistent
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    eval H (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) =
      eval native (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) := by
  exact ARU_OriginalFactory.original L copy allocator c err r native1 native2 hashv extraction a native H n syscall consistent

#print axioms original
end AspisR1.ARW_AdmittedSupport
end
