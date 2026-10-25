import DrvC_BatchDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_SecondCode
open Aeneas Aeneas.Std Result VTop_Stages
open DrvC_Installation DrvC_Effects DrvC_Flow
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult

theorem batch {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) :
    DrvC_CallCode.code c (.op5 (digest c) proof p root 1#usize ()) =
      SdkC_BatchSource.stageCode hashv proof p root := by
  unfold DrvC_CallCode.code SdkC_BatchSource.stageCode
  rw [DrvC_BatchDictionary.code (VTop_Checkpoint.digest (digest c)) (SdkC_Source.dictionary hashv)]

attribute [local irreducible] SdkC_BatchSource.stageCode GExp_RetainedReader.code

theorem common {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (pub proof checkpoint : Slice U8) :
    VTop_Flow.tx2_common (effects c) (digest c) pub proof checkpoint () none =
      GExp_SecondCode.common (stage c) c.reserved hashv (digest c) pub proof checkpoint := by
  have installed : GExp_SecondCode.installed (stage c) c.reserved = stage c :=
    GExp_SecondPair.installed (AuS1_Install.base c.stageBase) c.finish c.reserved c.query c.geometry
  simp only [VTop_Flow.tx2_common,GExp_SecondCode.common,installed,effects,batch]
  all_goals repeat' first
    | (with_reducible rfl)
    | (apply code_bind_congr; intro x)
    | split

#print axioms batch
#print axioms common
end AspisR1.DrvC_SecondCode
end
