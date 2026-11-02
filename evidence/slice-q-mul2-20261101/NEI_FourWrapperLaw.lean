import NEI_FourWrapper.Funs
set_option autoImplicit false
noncomputable section
namespace NEI_FourWrapperLaw
open Aeneas Aeneas.Std Result
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact
/-- The actual emitted wrapper, with the prefix conversion still explicit. -/
theorem same_four_calls (q : Slice U8) (g : Array E 29#usize) :
 NEI_FourWrapper.fast_dots.four_dots q g = (do
  let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) q {«end» := 608#usize}
  let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
  let q1 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let a ← AspisR1.FIp_NativeDots.fast_dots.four_dots_one q1 g 0#usize
  let b ← AspisR1.FIp_NativeDots.fast_dots.four_dots_one q1 g 1#usize
  let c ← AspisR1.FIp_NativeDots.fast_dots.four_dots_one q1 g 2#usize
  let d ← AspisR1.FIp_NativeDots.fast_dots.four_dots_one q1 g 3#usize
  ok (Array.make 4#usize [a,b,c,d])) := by rfl
/-- Slot arithmetic is unconditional; every child sees the same q/g carriers. -/
theorem slots : ∀ slot ∈ ([0,1,2,3] : List Nat), slot < 4 := by decide
#print axioms same_four_calls
#print axioms slots
end NEI_FourWrapperLaw
end
