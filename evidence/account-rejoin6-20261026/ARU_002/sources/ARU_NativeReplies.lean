import ARQ_Installation
import ARU_WrapperAccepted
import ARS_NativeAccount
import SCE_NativeFirst
import SCE_NativeSecond
import SCE_AcceptedOutcome
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_NativeReplies
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment SCE_Execution

/-- Pointwise same-world transfer at the exact Rc9 installation. Native
observations name the original choices, never independent successful inputs. -/
theorem accepted {A C : Type}
    (base : DrvC_Installation.Configuration FIo_Install.W C) (err : C)
    (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) native1 native2 hashv)
    (H : Bytes → State)
    (a : Adversary A) (id : S2W_ExtractionBoundary.Program)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (firstAgrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (ARS_NativeAccount.firstSyntax (FIp_Install.configuration err base reservation) hashv copy allocator id (eval H a.first).2) []).2)
    (secondAgrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (ARS_NativeAccount.secondSyntax (FIp_Install.configuration err base reservation) hashv allocator id
        (eval H (a.second (eval H a.first).2 saved post1 final1)).2) []).2)
    (one : first native1 copy allocator (eval H a.first).2.entry id
      (eval H a.first).2.data (eval H a.first).2.state = ok (.Ok (saved,post1,final1)))
    (two : let j := (eval H (a.second (eval H a.first).2 saved post1 final1)).2
      second native2 allocator j.entry id j.data j.slot j.state = ok (.Ok (post2,final2))) :
    let c := FIp_Install.configuration err base reservation
    (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 = ok (.Ok (saved,post1,final1)) ∧
    (eval H (secondCode c hashv allocator id
      (eval H (a.second (eval H a.first).2 saved post1 final1)).2)).2 = ok (.Ok (post2,final2)) ∧
    SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true := by
  dsimp only
  let c := FIp_Install.configuration err base reservation
  have ext : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) native1 native2 hashv := by
    rw [←ARQ_Installation.dictionary err base reservation]
    exact extraction
  have first := congrArg Prod.snd (ARU_WrapperAccepted.first c.adapter c.currentBase c.stageBase
    c.finish c.reserved c.query c.geometry c.boundaries c.std hashv copy allocator
    (eval H a.first).2.entry id (eval H a.first).2.data (eval H a.first).2.state
    native1 native2 ext H saved post1 final1 firstAgrees one)
  have second := congrArg Prod.snd (ARU_WrapperAccepted.second c.adapter c.currentBase c.stageBase
    c.finish c.reserved c.query c.geometry c.boundaries c.std hashv allocator
    (eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry id
    (eval H (a.second (eval H a.first).2 saved post1 final1)).2.data
    (eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot
    (eval H (a.second (eval H a.first).2 saved post1 final1)).2.state
    native1 native2 ext H post2 final2 secondAgrees two)
  exact ⟨first,second,SCE_AcceptedOutcome.from_source_calls c hashv copy allocator id a H saved
    post1 post2 final1 final2 first second⟩

#print axioms accepted
end AspisR1.ARU_NativeReplies
end
