import RPv_FJg_ScalarFold
import RPu_FGm_WideScaleValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ScalarValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)
/-- Actual scalar_factor fold and final quarter scaling, proved by symbolic
iterator induction and the existing native scale arithmetic. -/
theorem value (p : Array NE 4#usize) (f : Array NQ 4#usize) (hp : FIo_ArrayCanon.Holds p)
    (out : NE) (run : FIo_Native.weights.Weights.scalar_factor f p=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=
      decodeM FIo_Native.weights.QUARTER • FJg_ScalarCell.sumPrefix p f 4 := by
  unfold FIo_Native.weights.Weights.scalar_factor at run
  obtain ⟨sum,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have fold := FJg_ScalarFold.four p f hp sum hs
  have scale := FGm_WideScaleValue.value sum out FIo_Native.weights.QUARTER run
  exact ⟨scale.1,scale.2.trans (congrArg (fun x=>decodeM FIo_Native.weights.QUARTER • x) fold.2)⟩
#print axioms value
end AspisR1.FJg_ScalarValue
end
