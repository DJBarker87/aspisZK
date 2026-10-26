import SCE_FirstCutBytes
import SCE_SubmissionExt
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_CarriedCut
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open MultiproofConeCanonical SCE_Experiment F3T_ByteCarrier

theorem input_eq {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (a : Adversary A) (H : Bytes → State) (ops : AdapterRw.Ops)
    (accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops (eval H a.first).2.entry.first accounts2 saved f s) :
    (eval H (F3T_Canon.canon (lift c (submission a)))).2 =
      F3T_Canon.canonInput (input c ⟨bytesOf f.pub.val,bytesOf f.proof.val⟩) := by
  have bytes := SCE_FirstCutBytes.submitted_cut (eval H a.first).2 ops accounts2 saved f s cuts
  have same : submitted (eval H a.first).2 = (⟨bytesOf f.pub.val,bytesOf f.proof.val⟩ : Submission) :=
    SCE_SubmissionExt.equal _ _ bytes.1 bytes.2
  rw [F3T_Canon.canon_eval,lift_eval,submission_eval,same]

#print axioms input_eq
end AspisR1.SCE_CarriedCut
end
