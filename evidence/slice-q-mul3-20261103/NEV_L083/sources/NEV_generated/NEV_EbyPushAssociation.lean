import NEV_EbyPushRaw.Funs
import NEV_DotPush
import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace NEV_EbyPushAssociation
open Aeneas Aeneas.Std Result AspisR1
/-- Entire actual isolated Result, including rejected count/scalar and unchanged
receiver. The checked increment is derived from the actual count guard. -/
theorem source (self : NEV_EbyPushRaw.fast_pairing.EbyKDot)
    (value : NEV_EbyPushRaw.aspis_core.field.wide_exact.WideExact)
    (scalar : NEV_EbyPushRaw.aspis_core.field.QM31) :
    NEV_EbyPushRaw.fast_pairing.EbyKDot.push self value scalar =
      FIo_Native.fast_pairing.EbyKDot.push self value scalar := by
  unfold NEV_EbyPushRaw.fast_pairing.EbyKDot.push FIo_Native.fast_pairing.EbyKDot.push
  simp only [NEV_EbyPushRaw.fast_pairing.MAX_TERMS,FIo_Native.fast_pairing.MAX_TERMS]
  split_ifs with guard
  · rfl
  · have bound : self.count.val+1≤4096 := by omega
    have increment := Port3_Wrapping.checked_add self.count 1#usize (by simpa using bound)
    simp only [increment,bind_tc_ok,lift]
    rfl
#print axioms source
end NEV_EbyPushAssociation
end
