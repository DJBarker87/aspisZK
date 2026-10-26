import SCE_AdaptivePadding
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_PaddingFirstPass
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier SCE_Experiment SCE_Execution SCE_AdaptivePadding

/-- The first-only submission projection cannot satisfy accepted physical
first-pass equality for ALL adaptive adversaries: from ANY accepted account
run, one of it and its padded version disagrees. This is an interface theorem,
conditional on actual source acceptance, not a deployed attack fixture. -/
theorem not_both {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (address : Bytes) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      .ok (.Ok (saved,post,final)))
    (accepted : SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true)
    (rust : F3T_TwoPass.Verifier) :
    ¬ (SCC_Physical.FirstPassBinding rust (F3T_Canon.canon (lift c (submission a)))
        (runtime c hashv copy allocator id a) ∧
       SCC_Physical.FirstPassBinding rust (F3T_Canon.canon (lift c (submission (pad a address))))
        (runtime c hashv copy allocator id (pad a address))) := by
  rintro ⟨base,padded⟩
  let v := eval H (account c hashv copy allocator id a)
  let u := eval H (account c hashv copy allocator id (pad a address))
  let rb : RunView := (v.1,(F3T_Canon.canonInput (input c (submitted v.2.1)),SCE_Experiment.accepted v.2))
  let rp : RunView := (u.1,(F3T_Canon.canonInput (input c (submitted u.2.1)),SCE_Experiment.accepted u.2))
  have ob : (eval H (runtime c hashv copy allocator id a)).2 = some rb := by rw [runtime_eval]
  have op : (eval H (runtime c hashv copy allocator id (pad a address))).2 = some rp := by rw [runtime_eval]
  have ab : rb.2.2 = true := accepted
  have ap : rp.2.2 = true := by
    change SCE_Experiment.accepted u.2 = true
    rw [outcome_same c hashv copy allocator id a address H saved post final first]
    exact accepted
  have sameBase := base H rb ob ab
  have samePad := padded H rp op ap
  rw [submission_same] at samePad
  have same := sameBase.trans samePad.symm
  have lengths := congrArg (fun r : RunView => r.1.length) same
  have longer := log_length c hashv copy allocator id a address H saved post final first
  change v.1.length = u.1.length at lengths
  change u.1.length = v.1.length+1 at longer
  omega

#print axioms not_both
end AspisR1.SCE_PaddingFirstPass
end
