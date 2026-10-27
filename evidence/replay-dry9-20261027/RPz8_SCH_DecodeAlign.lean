import RPz8_SCH_DigestAlign
import RPz8_SCH_ChildUpdate
set_option autoImplicit false
namespace AspisR1.SCH_DecodeAlign
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem update (o k : AdapterRw.Ops) :
    Port1_Driver.decodeSemantic (SCH_ChildUpdate.update o k) = Port1_Driver.decodeSemantic o := rfl

theorem installed {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State) :
    let r := Rc5_Install.configuration err c reservation
    Port1_Driver.decodeSemantic (SCH_IdealSdk.dictionary r hashv H) =
      Port1_Driver.decodeSemantic (DrvC_Installation.sdk r) := by
  dsimp only
  have aligned : AuS1_Install.base (Rc5_Install.configuration err c reservation).stageBase =
      (Rc5_Install.configuration err c reservation).stageBase := SCH_StageAlign.library _
  rw [DrvC_Installation.gexp_dictionary,aligned]
  exact (congrArg Port1_Driver.decodeSemantic (SCH_ChildUpdate.original _ hashv H)).trans (update _ _)

#print axioms update
#print axioms installed
end AspisR1.SCH_DecodeAlign
