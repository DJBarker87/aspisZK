import NFF_LoggedOne
import NFE_WrapperBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFF_LoggedWrapper
open Aeneas Aeneas.Std Result

def run (oracle : NFF_LoggedEight.Oracle) (q : Slice U8)
    (g : NEV_DotInputs.Coefficients) : Result (Array NEV_DotCarrier.NE 4#usize) := do
  let window ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    q {«end»:=608#usize}
  let converted ← core.array.TryFromSharedArraySlice.try_from 608#usize window
  let fixed ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted
  let a ← NFF_LoggedOne.run oracle fixed g 0#usize
  let b ← NFF_LoggedOne.run oracle fixed g 1#usize
  let c ← NFF_LoggedOne.run oracle fixed g 2#usize
  let d ← NFF_LoggedOne.run oracle fixed g 3#usize
  ok (Array.make 4#usize [a,b,c,d])

theorem replay (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (q : Slice U8) (g : NEV_DotInputs.Coefficients) (domain : NEV_DotInputs.Canonical g) :
    run oracle q g=FIp_NativeDots.fast_dots.four_dots q g := by
  simp only [run,FIp_NativeDots.fast_dots.four_dots,
    NFF_LoggedOne.replay oracle law _ g domain]

theorem headline (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (q : Slice U8) (g : NEV_DotInputs.Coefficients) (domain : NEV_DotInputs.Canonical g) :
    run oracle q g=NEI_FourWrapper.fast_dots.four_dots q g := by
  rw [replay oracle law q g domain,NEI_FourWrapperLaw.emitted_to_cohort]
  exact NEV_FourResult.source q g |>.symm

#print axioms replay
#print axioms headline
end AspisR1.NFF_LoggedWrapper
end
