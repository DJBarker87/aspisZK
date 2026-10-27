import RPt_BEn_ReachedLaws
import RPz8_ARU_Support
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEn_AdmittedCuts
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation SdkC_Source

/-- Same admitted account's reached operands and all-outcome local laws.
No global P1/RuntimeSyscall at H is required. -/
theorem selected {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (std : S2W_TrustedStd.TrustedStd copy) :
    let cfg := FIp_Install.configuration err c r
    ∃ f s, SourceCuts (DrvC_Installation.sdk cfg) (eval H a.first).2.entry.first
      ((eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.second secondSizes)
      n.entry.saved f s ∧
      n.entry.post2 = (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.heap ∧
      ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Digest)
        (p1 : VTop_Stages.verifier.Prepared) (root1 : Digest),
        Op5T_Install.currentBatch Port4B_Install.leaves (DrvC_Installation.currentDigest cfg)
          f.proof p0 root0 0#usize () = ok (.Ok ()) ∧
        Op5T_Install.stageBatch Port4B_Install.leaves (DrvC_Installation.digest cfg)
          s.proof p1 root1 1#usize () = ok (.Ok ()) ∧
        ∀ (S : Type) (call : Parts → S → Result Digest × S) (state : S) (before : Log),
          BEh_Scope.Law
            (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.currentBody hashv f.proof p0 root0) state before)
            (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv f.proof p0 root0) state before) ∧
          BEh_Scope.Law
            (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.stageBody hashv s.proof p1 root1) state before)
            (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv s.proof p1 root1) state before) := by
  exact BEn_ReachedLaws.cuts (FIp_Install.configuration err c r) copy std allocator
    (eval H a.first).2.entry
    (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry
    CPH_Program.verifier native1 native2 hashv extraction
    (eval H a.first).2.data
    (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.data
    (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.slot
    (eval H a.first).2.state
    (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.state
    n.entry.final1 n.entry.final2 n.entry.saved n.entry.post1 n.entry.post2 n.entry.accepted1 n.entry.accepted2

#print axioms selected
end AspisR1.BEn_AdmittedCuts
end
