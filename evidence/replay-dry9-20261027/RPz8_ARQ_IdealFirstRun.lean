import RPz8_ARQ_ChildDigest
import RPz8_ARQ_FirstIdeal
import RPz8_F3V_RunEvidence
import F3U_ReifyValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_IdealFirstRun
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation

/-- Convert the actual ideal first child to the existing typed accepted
branch on those SAME operands. No native wrapper success is an input. -/
theorem typed {F C : Type} (c : Configuration F C)
    (aligned : sdk c = GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (called : (SCH_IdealSdk.dictionary c hashv H).op10
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (SCH_IdealSdk.dictionary c hashv H))
        semantic pub proof split () none = ok (.Ok saved)) :
    AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std)
      (F3V_RunEvidence.D1 c H) (AspisS6CurrentVerifierCarrier.toPublic semantic)
      pub proof split () none = ok (.Ok saved) := by
  have code := ARQ_FirstIdeal.code c hashv H semantic pub proof split saved called
  rw [←ARQ_ChildDigest.current c aligned] at code
  have erased := (F3U_ReifyValue.value _ H).symm.trans code
  rw [F3V_FirstCode.same H] at erased
  rw [GExp_FirstSource.source _ c.boundaries c.std (F3U_Oracle.hashv H)
    (F3V_RunEvidence.D1 c H) (fun _ => rfl)] at erased
  exact erased

/-- The accepted first child's reached guard fixes the split at ten. -/
theorem split {F C : Type} (c : Configuration F C)
    (aligned : sdk c = GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (k : Usize) (saved : alloc.vec.Vec U8)
    (called : (SCH_IdealSdk.dictionary c hashv H).op10
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (SCH_IdealSdk.dictionary c hashv H))
        semantic pub proof k () none = ok (.Ok saved)) : k = 10#usize := by
  have facts := AspisR1CurrentCaller.Tx1Reachability.tx1_success _ _
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof k () saved
    (typed c aligned hashv H semantic pub proof k saved called)
  simpa only [AspisR1CurrentCaller.compact.SPLIT] using facts.1

#print axioms typed
#print axioms split
end AspisR1.ARQ_IdealFirstRun
end
