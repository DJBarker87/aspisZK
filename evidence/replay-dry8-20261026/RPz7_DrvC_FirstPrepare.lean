import RPz7_DrvC_CurrentSlots
import RPz7_DrvC_MapCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstPrepare
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers DrvC_CurrentSlots

theorem code {F C : Type} (c : Configuration F C) (semantic : Port1_Driver.Semantic)
    (proof : Slice U8) (g : Array Tx1Q_Carriers.C.E 29#usize) :
    DrvC_CallCode.code c (.op7 (digest c) semantic proof () none (arr e g)) =
      DrvC_Program.mapCode DrvC_Dictionary.prepareReply
        (SdkD_PrepareLower.lower (SdkD_PrepareSource.code
          (Op5T_Concrete.current
            {GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry with op16 := Tx1Q_Install.writer})
          c.boundaries c.std (currentDigest c)
          (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () g)) := by
  change DrvC_Implementation.prepare c (digest c) semantic proof () (arr e g) = _
  dsimp only [DrvC_Implementation.prepare]
  rw [arr_roundtrip e unE unE_e,current_base]
  rfl

theorem writer {F C : Type} (c : Configuration F C)
    (p : Tx1Q_Carriers.C.P) (a : Tx1Q_Carriers.C.A) (proof pub : Slice U8) :
    DrvC_CallCode.code c (.op8 (digest c) (prepared p) (accumulator a) proof pub ()) =
      GExp_FirstCode.writerCode p a proof pub := by
  change GExp_FirstCode.writerCode (DrvC_Carriers.unPrepared (prepared p))
    (unAccumulator (accumulator a)) proof pub = _
  rw [DrvC_Carriers.current_prepared_roundtrip,current_roundtrip]

#print axioms code
#print axioms writer
end AspisR1.DrvC_FirstPrepare
end
