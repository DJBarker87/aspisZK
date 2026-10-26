import RPz7_DrvC_Flow
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_SecondFlow
open Aeneas Aeneas.Std Result VTop_Stages
open DrvC_Installation DrvC_Effects DrvC_Flow
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult
theorem tx2_common {F C H : Type} (c : Configuration F C)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub proof checkpoint : Slice U8)
    (obs : Option (verifier.Phase → Result Unit)) :
    DrvC_CallCode.lower c (VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof checkpoint hash obs) =
      VTop_Flow.tx2_common (effects c) D pub proof checkpoint hash obs := by
  simp only [VTop_Flow.tx2_common,VTop_Flow.traceEffects,effects,
    lower_bindM,lower_liftM,lower_pure,lower_perform,lower_if]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp_all only [lower_bindM,lower_liftM,lower_pure,lower_perform,lower_if])
    | (apply code_bind_congr; intro x)
    | split


theorem tx2_authenticated {F C H : Type} (c : Configuration F C)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit)) :
    DrvC_CallCode.lower c (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof checkpoint hash obs) =
      VTop_Flow.tx2_authenticated (effects c) D pub proof checkpoint hash obs := by
  simp only [VTop_Flow.tx2_authenticated,
    lower_bindM,lower_liftM,lower_pure,lower_perform,lower_if,tx2_common]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp_all only [lower_bindM,lower_liftM,lower_pure,lower_perform,lower_if,tx2_common])
    | (apply code_bind_congr; intro x)
    | split

#print axioms tx2_common
#print axioms tx2_authenticated
end AspisR1.DrvC_SecondFlow
end
