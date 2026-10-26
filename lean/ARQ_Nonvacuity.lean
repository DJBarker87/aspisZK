import ARQ_NativeReplies
import JFx_NativeBytes
import ARQ_Installation
import SCE_NativeFirst
import SCE_NativeSecond
import SCE_AcceptedOutcome
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment SCE_Execution

/-- Pending JFr fixture obligation, stated on genuine extracted wrappers.
This result is CONDITIONAL on JFr's accepted real-byte pair; it never uses
SCE_FixtureData.n1/n2 or claims that the obligation is already inhabited. -/
theorem accepted {A C : Type}
    (base : DrvC_Installation.Configuration FIo_Install.W C) (err : C)
    (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (a : Adversary A) (id : S2W_ExtractionBoundary.Program)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (realBytes : (eval H (submission a)).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission))
    (one : first native1 copy allocator (eval H a.first).2.entry id
      (eval H a.first).2.data (eval H a.first).2.state = ok (.Ok (saved,post1,final1)))
    (two : let j := (eval H (a.second (eval H a.first).2 saved post1 final1)).2
      second native2 allocator j.entry id j.data j.slot j.state = ok (.Ok (post2,final2))) :
    let c := FIp_Install.configuration err base reservation
    (eval H (submission a)).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission) ∧
    (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 = ok (.Ok (saved,post1,final1)) ∧
    (eval H (secondCode c hashv allocator id
      (eval H (a.second (eval H a.first).2 saved post1 final1)).2)).2 = ok (.Ok (post2,final2)) ∧
    SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true := by
  exact ⟨realBytes,ARQ_NativeReplies.accepted base err reservation hashv copy allocator native1 native2
    extraction sha256 H p1 syscall a id saved post1 post2 final1 final2 one two⟩

#print axioms accepted
end AspisR1.ARQ_Nonvacuity
end
