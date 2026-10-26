import SCH_IdealSdk
set_option autoImplicit false
namespace AspisR1.SCH_ChildUpdate

def update (original children : AdapterRw.Ops) : AdapterRw.Ops :=
  { original with op10 := children.op10, op11 := children.op11 }

/-- Isolate the two changed fields before comparing large source helpers. -/
theorem original {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : AspisR1.SdkC_Source.Parts → Aeneas.Std.Result AspisR1.SdkC_Source.Digest)
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) :
    SCH_IdealSdk.dictionary c hashv H =
      update (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) (SCH_IdealSdk.dictionary c hashv H) := rfl

#print axioms original
end AspisR1.SCH_ChildUpdate
