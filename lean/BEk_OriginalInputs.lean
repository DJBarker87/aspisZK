import BEk_ReachedInputs
import ARU_OriginalFactory
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_OriginalInputs
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
/-- Reached native-source arguments AND queried-address support on the original
account cylinder. The fixed native execution is retained. No physical internal
batch heap/recorder is inferred from these source arguments. -/
theorem selected {W A C Tx : Type} (L : Library W (Nat → Record))
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
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H) :
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
          s.proof p1 root1 1#usize () = ok (.Ok ()) := by
  obtain ⟨supported,same⟩ := ARU_OriginalFactory.original L copy allocator c err r
    native1 native2 hashv extraction a native H n syscall consistent
  obtain ⟨f,s,cuts,frame,batches⟩ := BEk_ReachedInputs.cuts (FIp_Install.configuration err c r)
    copy std allocator (eval native a.first).2.entry
    (eval native (a.second (eval native a.first).2 n.saved n.post1 n.final1)).2.entry
    CPH_Program.verifier native1 native2 hashv extraction
    (eval native a.first).2.data
    (eval native (a.second (eval native a.first).2 n.saved n.post1 n.final1)).2.data
    (eval native (a.second (eval native a.first).2 n.saved n.post1 n.final1)).2.slot
    (eval native a.first).2.state
    (eval native (a.second (eval native a.first).2 n.saved n.post1 n.final1)).2.state
    n.final1 n.final2 n.saved n.post1 n.post2 n.accepted1 n.accepted2
  exact ⟨supported,same,f,s,cuts,batches⟩

#print axioms selected
end AspisR1.BEk_OriginalInputs
end
