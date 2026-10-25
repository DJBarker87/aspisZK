import DrvC_CallCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Effects
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace
open DrvC_Installation
def effects {F C : Type} (c : Configuration F C) : VTop_Flow.Effects SdkC_Source.Code := {
  op0 := fun {T} {E} a0 a1 => DrvC_CallCode.code c (.op0 (T := T) (E := E) a0 a1)
  op1 := DrvC_CallCode.code c (.op1 )
  op2 := fun a0 => DrvC_CallCode.code c (.op2 a0)
  op3 := fun a0 => DrvC_CallCode.code c (.op3 a0)
  op4 := fun a0 => DrvC_CallCode.code c (.op4 a0)
  op5 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => DrvC_CallCode.code c (.op5 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
  op6 := fun a0 a1 a2 a3 a4 a5 a6 a7 => DrvC_CallCode.code c (.op6 a0 a1 a2 a3 a4 a5 a6 a7)
  op7 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => DrvC_CallCode.code c (.op7 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
  op8 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => DrvC_CallCode.code c (.op8 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
  op9 := fun a0 a1 => DrvC_CallCode.code c (.op9 a0 a1)
  op10 := fun a0 => DrvC_CallCode.code c (.op10 a0)
  op11 := fun a0 a1 a2 => DrvC_CallCode.code c (.op11 a0 a1 a2)
  op12 := fun a0 => DrvC_CallCode.code c (.op12 a0)
  op13 := fun a0 a1 => DrvC_CallCode.code c (.op13 a0 a1)
  op14 := DrvC_CallCode.code c (.op14 )
  op15 := DrvC_CallCode.code c (.op15 )
  op16 := DrvC_CallCode.code c (.op16 )
  op17 := fun N a0 => DrvC_CallCode.code c (.op17 N a0)
  op18 := fun {H} aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 => DrvC_CallCode.code c (.op18 (H := H) aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
  op19 := fun a0 a1 a2 a3 => DrvC_CallCode.code c (.op19 a0 a1 a2 a3)
  op20 := DrvC_CallCode.code c (.op20 )
  op21 := DrvC_CallCode.code c (.op21 )
  op22 := DrvC_CallCode.code c (.op22 )
  op23 := DrvC_CallCode.code c (.op23 )
  unwrap32 := fun a0 => DrvC_CallCode.code c (.unwrap32 a0)
}


theorem bind_assoc {A B D : Type} (p : SdkC_Source.Code A)
    (k : A → SdkC_Source.Code B) (h : B → SdkC_Source.Code D) :
    CheckpointBytes5Effect.bind (CheckpointBytes5Effect.bind p k) h =
      CheckpointBytes5Effect.bind p (fun a => CheckpointBytes5Effect.bind (k a) h) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    simp only [CheckpointBytes5Effect.bind]
    congr 1
    funext a
    exact ih a
  | read parts next ih =>
    simp only [CheckpointBytes5Effect.bind]
    congr 1
    funext a
    exact ih a

theorem bind_pure {A : Type} (p : SdkC_Source.Code A) :
    CheckpointBytes5Effect.bind p CheckpointBytes5Effect.Code.done = p := by
  induction p with
  | done a => rfl
  | step r next ih =>
    simp only [CheckpointBytes5Effect.bind]
    congr 1
    funext a
    exact ih a
  | read parts next ih =>
    simp only [CheckpointBytes5Effect.bind]
    congr 1
    funext a
    exact ih a

theorem lower_bind {F C A B : Type} (c : Configuration F C)
    (p : VTop_Trace.Code A) (k : A → VTop_Trace.Code B) :
    DrvC_CallCode.lower c (VTop_Trace.bind p k) =
      CheckpointBytes5Effect.bind (DrvC_CallCode.lower c p) (fun a => DrvC_CallCode.lower c (k a)) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    simp only [VTop_Trace.bind,DrvC_CallCode.lower,CheckpointBytes5Effect.bind]
    congr 1
    funext a
    exact ih a
  | call op next ih =>
    simp only [VTop_Trace.bind,DrvC_CallCode.lower]
    rw [bind_assoc]
    congr 1
    funext a
    exact ih a

theorem lower_lift {F C A : Type} (c : Configuration F C) (r : Result A) :
    DrvC_CallCode.lower c (VTop_Trace.liftResult r) = CheckpointBytes5Effect.liftResult r := rfl

theorem lower_perform {F C A : Type} (c : Configuration F C) (op : VTop_Trace.Call A) :
    DrvC_CallCode.lower c (VTop_Trace.perform op) = DrvC_CallCode.code c op := by
  simp only [VTop_Trace.perform,DrvC_CallCode.lower,bind_pure]

#print axioms bind_assoc
#print axioms bind_pure
#print axioms lower_bind
#print axioms lower_lift
#print axioms lower_perform
end AspisR1.DrvC_Effects
end
