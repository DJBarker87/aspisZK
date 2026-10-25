import DrvC_FirstHeadSyntax
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstHeadBridge
open Aeneas Aeneas.Std Result
open DrvC_Installation
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult

theorem stage {F C : Type} (c : Configuration F C)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (k : Usize) :
    VTop_Flow.tx1 (DrvC_Effects.effects c) (digest c) semantic pub proof k () none =
      DrvC_FirstHeadSyntax.stageHead c semantic pub proof k := rfl

theorem source {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (k : Usize) :
    GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std hashv (currentDigest c)
      (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof k =
    DrvC_FirstHeadSyntax.sourceHead c hashv semantic pub proof k := by
  unfold GExp_FirstCode.code DrvC_FirstHeadSyntax.sourceHead DrvC_FirstSyntax.sourceTail
  rw [← current_dictionary]
  rfl

#print axioms stage
#print axioms source
end AspisR1.DrvC_FirstHeadBridge
end
