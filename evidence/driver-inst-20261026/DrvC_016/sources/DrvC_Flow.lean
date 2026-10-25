import DrvC_Effects
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Flow
open Aeneas Aeneas.Std Result VTop_Stages
open DrvC_Installation DrvC_Effects
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult

theorem lower_pure {F C A : Type} (c : Configuration F C) (a : A) :
    DrvC_CallCode.lower c (pure a) = (pure a : SdkC_Source.Code A) := rfl

theorem lower_liftM {F C A : Type} (c : Configuration F C) (r : Result A) :
    DrvC_CallCode.lower c (monadLift r : VTop_Trace.Code A) =
      (monadLift r : SdkC_Source.Code A) := rfl

theorem lower_if {F C A : Type} (c : Configuration F C) (p : Prop) [Decidable p]
    (yes no : VTop_Trace.Code A) :
    DrvC_CallCode.lower c (if p then yes else no) =
      if p then DrvC_CallCode.lower c yes else DrvC_CallCode.lower c no := by split <;> rfl

theorem code_bind_congr {A B : Type} (p : SdkC_Source.Code A)
    (k h : A → SdkC_Source.Code B) (eq : ∀ a, k a = h a) :
    (p >>= k) = (p >>= h) := congrArg (fun f => p >>= f) (funext eq)

theorem tx1 {F C H : Type} (c : Configuration F C)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (split : Usize)
    (obs : Option (verifier.Phase → Result Unit)) :
    DrvC_CallCode.lower c (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof split hash obs) =
      VTop_Flow.tx1 (effects c) D semantic pub proof split hash obs := by
  simp only [VTop_Flow.tx1,VTop_Flow.traceEffects,effects,
    lower_bind,lower_liftM,lower_pure,lower_perform,lower_if]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp_all only [lower_bind,lower_liftM,lower_pure,lower_perform,lower_if])
    | (apply code_bind_congr; intro x)
    | split

#print axioms lower_pure
#print axioms lower_liftM
#print axioms lower_if
#print axioms code_bind_congr
#print axioms tx1
end AspisR1.DrvC_Flow
end
