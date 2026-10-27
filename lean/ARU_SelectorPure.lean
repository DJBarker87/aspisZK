import ARQ_Installation
import SCH_UpdateValidate
import SCG_Selection
import P2P_NativeSelection
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_SelectorPure
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)

theorem account : Hiq_ByteSelection.account (SCH_IdealSdk.dictionary c hashv H) =
    Hiq_ByteSelection.account (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std) := by
  funext accounts slot
  unfold Hiq_ByteSelection.account
  rw [SCH_SdkPure.data]

theorem public2 : Hiq_ByteSelection.public2 (SCH_IdealSdk.dictionary c hashv H) =
    Hiq_ByteSelection.public2 (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std) := by
  funext id accounts data slot
  unfold Hiq_ByteSelection.public2
  rw [SCH_ChildUpdate.original,SCH_UpdateValidate.same]
  rfl

theorem pair (id : S2W_ExtractionBoundary.Program) (e1 e2 : S2W_D189Entry.Entry)
    (data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    P2P_NativeSelection.pair (SCH_IdealSdk.dictionary c hashv H) id e1 e2 data2 slot =
    P2P_NativeSelection.pair (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std) id e1 e2 data2 slot := by
  unfold P2P_NativeSelection.pair
  rw [account,public2]

#print axioms account
#print axioms public2
#print axioms pair
end AspisR1.ARU_SelectorPure
end
