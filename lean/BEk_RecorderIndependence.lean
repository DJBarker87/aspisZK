import BEk_OriginalInputs
import BEi_PhysicalGap
import ARU_OriginalFactory
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_RecorderIndependence
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
/-- Even after deriving ARU's ORIGINAL queried-address cylinder and concrete
reached source arguments, value/carrier observations do not determine an
independently supplied physical recorder. This is an interface non-implication,
NOT a native-code counterexample and NOT an alternative physical execution. -/
theorem original {W A C Tx S : Type} (L : Library W (Nat → Record))
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
    (std : S2W_TrustedStd.TrustedStd copy)
    (consistent : ARS_AccountReplay.Consistent
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H)
    (call : SdkC_Source.Parts → S → Result SdkC_Source.Digest × S)
    (state : S) (before : SdkC_Source.Log) (extra : SdkC_Source.Query) :
    let cfg := FIp_Install.configuration err c r
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    eval H (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a) =
      eval native (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a) ∧
    ∃ f s, SourceCuts (DrvC_Installation.sdk cfg) (eval native a.first).2.entry.first
      ((eval native (a.second (eval native a.first).2 n.saved n.post1 n.final1)).2.entry.second secondSizes)
      n.saved f s ∧
      ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
        (p1 : VTop_Stages.verifier.Prepared) (root1 : Array U8 32#usize),
        Op5T_Install.currentBatch Port4B_Install.leaves (DrvC_Installation.currentDigest cfg)
          f.proof p0 root0 0#usize () = ok (.Ok ()) ∧
        Op5T_Install.stageBatch Port4B_Install.leaves (DrvC_Installation.digest cfg)
          s.proof p1 root1 1#usize () = ok (.Ok ()) ∧
        ∃ other : BEh_Scope.Outcome S Unit AspisR1CurrentCaller.verifier.Error,
          other.1 = (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv f.proof p0 root0) state before).1 ∧
          other.2.1 = (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv f.proof p0 root0) state before).2.1 ∧
          ¬ BEh_Scope.Law other
            (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv f.proof p0 root0) state before) := by
  obtain ⟨supported,same,f,s,cuts,p0,root0,p1,root1,first,second⟩ :=
    BEk_OriginalInputs.selected L copy allocator c err r native1 native2 hashv extraction
      a native H n syscall std consistent
  have gap := BEi_PhysicalGap.extension
    (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv f.proof p0 root0) state before) extra
  refine ⟨supported,same,f,s,cuts,p0,root0,p1,root1,first,second,?_⟩
  let out := BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv f.proof p0 root0) state before
  exact ⟨(out.1,out.2.1,out.2.2 ++ [extra]),gap.1,gap.2.1,gap.2.2.2⟩

#print axioms original
end AspisR1.BEk_RecorderIndependence
end
