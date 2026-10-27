import RPz7_DrvC_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_AuthenticatedCode
open Aeneas Aeneas.Std Result VTop_Stages
open DrvC_Installation DrvC_Effects DrvC_Flow
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult

attribute [local irreducible] VTop_Flow.tx2_common GExp_SecondCode.common

theorem code {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (pub proof checkpoint : Slice U8) :
    VTop_Flow.tx2_authenticated (effects c) (digest c) pub proof checkpoint () none =
      GExp_SecondCode.code (stage c) c.reserved hashv (digest c) pub proof checkpoint := by
  have installed : GExp_SecondCode.installed (stage c) c.reserved = stage c :=
    GExp_SecondPair.installed (AuS1_Install.base c.stageBase) c.finish c.reserved c.query c.geometry
  simp only [VTop_Flow.tx2_authenticated,GExp_SecondCode.code,installed]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [DrvC_SecondCode.common c hashv])
    | (apply code_bind_congr; intro x)
    | split

#print axioms code
end AspisR1.DrvC_AuthenticatedCode
end
