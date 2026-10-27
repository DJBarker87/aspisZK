import RPz8_ARQ_FirstBytes
import RPz8_ARQ_FirstBody
import RPz8_ARQ_IdealFirstRun
import RPz8_ARQ_DecodeAlignment
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_ActualFirst
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution GExq_AccountExperiment DrvC_Installation

/-- First-child acceptance, decoded semantic value, ORIGINAL input bytes,
actual saved Vec, split-ten and exact wrapper log, on this H alone.
No second-wrapper or standalone-source success is assumed. -/
theorem accepted {A F C : Type} (c : Configuration F C)
    (aligned : sdk c = GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (H : Bytes → State)
    (success : (eval H (firstCode c hashv copy allocator id i)).2 = ok (.Ok (saved,post,final))) :
    ∃ semantic pub proof,
      submitted i = (⟨MultiproofConeCanonical.bytesOf pub.val,MultiproofConeCanonical.bytesOf proof.val⟩ : F3T_ByteCarrier.Submission) ∧
      Port1_Driver.decodeSemantic (sdk c) pub = ok (some semantic) ∧
      AspisR1CurrentCaller.verifier.candidate.tx1
        (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
        (F3V_RunEvidence.D1 c H) (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize () none = ok (.Ok saved) ∧
      (eval H (firstCode c hashv copy allocator id i)).1 =
        (eval H (SdkC_Oracle.program
          (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
            c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic)
            pub proof 10#usize))).1 := by
  obtain ⟨log,ran,same⟩ := ARQ_FirstBody.accepted c hashv copy allocator id i saved post final H success
  obtain ⟨semantic,pub,proof,split,answer,fields,decoded,first,projected,logs⟩ :=
    ARQ_FirstOperandsBytes.first c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std hashv id i.entry.first i.data saved log H ran
  obtain ⟨pa,pu,raw,index0,index1,rawRead,pubRead,range⟩ := fields
  have bytes := ARQ_FirstBytes.original i _ pa pu raw pub proof index0 index1 rawRead pubRead range
  have called := AspisS6CurrentStage1CodecJoin.first_success _ semantic pub proof split saved first
  have ten := ARQ_IdealFirstRun.split c aligned hashv H semantic pub proof split saved called
  subst split
  refine ⟨semantic,pub,proof,bytes,?_,ARQ_IdealFirstRun.typed c aligned hashv H semantic pub proof 10#usize saved called,?_⟩
  · rw [ARQ_DecodeAlignment.decode c aligned hashv H] at decoded
    exact decoded
  · rw [same,logs,←ARQ_ChildDigest.current c aligned]

#print axioms accepted
end AspisR1.ARQ_ActualFirst
end
