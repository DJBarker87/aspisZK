import RPu_FJf_EbyKPush
import RPu_FJf_EbyKFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_EbyKNew
open Aeneas Aeneas.Std Result

theorem value (out : FIo_Native.fast_pairing.EbyKDot)
    (run : FIo_Native.fast_pairing.EbyKDot.new=ok out) :
    out.count.val=0 ∧ FJf_EbyKCodec.Bound out ∧ FJf_EbyKCodec.model out=0 := by
  unfold FIo_Native.fast_pairing.EbyKDot.new FIo_Native.fast_pairing.canonical.Dot.new at run
  simp only [bind_tc_ok] at run
  cases Result.ok.inj run
  refine ⟨by decide,?_,?_⟩
  · constructor <;> intro j hj <;> interval_cases j <;> rfl
  · rfl
#print axioms value
end AspisR1.FJf_EbyKNew
end
