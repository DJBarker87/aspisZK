import ARQ_ChildDigest
import SCH_DecodeAlign
set_option autoImplicit false
namespace AspisR1.ARQ_DecodeAlignment
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation

theorem decode {F C : Type} (c : Configuration F C)
    (aligned : sdk c = GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State) :
    Port1_Driver.decodeSemantic (SCH_IdealSdk.dictionary c hashv H) = Port1_Driver.decodeSemantic (sdk c) := by
  rw [SCH_ChildUpdate.original,SCH_DecodeAlign.update,←aligned]

#print axioms decode
end AspisR1.ARQ_DecodeAlignment
