import RPz8_SCE_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_Physical
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier SCE_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)

/-- Exact remaining physical projections after the shared-adversary byte
association. This is an equivalence for review, not an assumed runtime law. -/
theorem run_eq_iff (run : RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run)
    (rust : F3T_TwoPass.Verifier) :
    run = eval H (F3T_TwoPass.originalWith rust (F3T_Canon.canon (lift c (submission a)))) ↔
      run.1 = (eval H (F3T_TwoPass.originalWith rust (F3T_Canon.canon (lift c (submission a))))).1 ∧
      run.2.2 = (eval H (rust (eval H (F3T_Canon.canon (lift c (submission a)))).2)).2 := by
  constructor
  · intro same
    subst run
    exact ⟨rfl,by rw [F3T_TwoPass.original_eval]⟩
  · rintro ⟨log,accept⟩
    apply Prod.ext log
    apply Prod.ext
    · rw [SCE_Projection.input_projection c hashv copy allocator id a H run observed,
        F3T_TwoPass.original_eval]
    · rw [F3T_TwoPass.original_eval]
      exact accept

/-- The actual physical chronological obligation, now stated entirely on
account and single-verifier executions. Projection does not prove it. -/
theorem chronological_iff (run : RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run)
    (rust : F3T_TwoPass.Verifier) :
    run.1 = (eval H (F3T_TwoPass.originalWith rust (F3T_Canon.canon (lift c (submission a))))).1 ↔
      (eval H (account c hashv copy allocator id a)).1 =
        (eval H a.first).1 ++
          (eval H (rust (F3T_Canon.canonInput (input c (submitted (eval H a.first).2))))).1 := by
  rw [SCE_Projection.chronological c hashv copy allocator id a H run observed,
    F3T_TwoPass.original_eval,F3T_Canon.canon_eval,lift_eval,submission_eval]

#print axioms run_eq_iff
#print axioms chronological_iff
end AspisR1.SCE_Physical
end
