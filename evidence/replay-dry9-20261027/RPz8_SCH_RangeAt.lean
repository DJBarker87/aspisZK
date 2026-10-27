import RPz8_SCH_SdkSecond
set_option autoImplicit false
namespace AspisR1.SCH_RangeAt
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem same {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State) (T : Type) :
    AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice (SCH_IdealSdk.dictionary c hashv H) T =
      AdapterRw.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
        (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std) T :=
  congrFun (SCH_SdkSecond.range c hashv H) T

#print axioms same
end AspisR1.SCH_RangeAt
