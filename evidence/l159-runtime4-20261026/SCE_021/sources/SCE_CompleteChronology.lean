import SCE_CompleteSubmission
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_CompleteChronology
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_ByteCarrier F3T_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)

theorem full_first_iff_empty_suffix (run : RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run)
    (rust : F3T_TwoPass.Verifier) :
    run.1 = (eval H (F3T_TwoPass.originalWith rust
      (F3T_Canon.canon (lift c (SCE_CompleteSubmission.program c hashv copy allocator id a))))).1 ↔
      (eval H (rust (eval H (F3T_Canon.canon
        (lift c (SCE_CompleteSubmission.program c hashv copy allocator id a)))).2)).1 = [] := by
  rw [SCE_Projection.chronological c hashv copy allocator id a H run observed,
    F3T_TwoPass.original_eval,F3T_Canon.canon_eval,lift_eval,
    SCE_CompleteSubmission.evaluation]
  constructor
  · intro same
    have lengths := congrArg List.length same
    simp only [List.length_append] at lengths
    have zero : (eval H (rust (F3T_Canon.canonInput (input c (eval H (submission a)).2))))).1.length = 0 := by
      omega
    exact List.length_eq_zero.mp zero
  · intro empty
    rw [empty,List.append_nil]

#print axioms full_first_iff_empty_suffix
end AspisR1.SCE_CompleteChronology
end
