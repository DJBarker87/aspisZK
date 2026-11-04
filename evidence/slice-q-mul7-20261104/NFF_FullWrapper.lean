import NFF_FullOne
import NFE_WrapperBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFF_FullWrapper
open Aeneas Aeneas.Std Result

def run (oracle : NFF_LoggedEight.Oracle) (tailOracle : NFF_ProductCall.Oracle) (q : Slice U8)
    (g : NEV_DotInputs.Coefficients) : Result (Array NEV_DotCarrier.NE 4#usize) := do
  let window ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    q {«end»:=608#usize}
  let converted ← core.array.TryFromSharedArraySlice.try_from 608#usize window
  let fixed ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted
  let a ← NFF_FullOne.run oracle tailOracle fixed g 0#usize
  let b ← NFF_FullOne.run oracle tailOracle fixed g 1#usize
  let c ← NFF_FullOne.run oracle tailOracle fixed g 2#usize
  let d ← NFF_FullOne.run oracle tailOracle fixed g 3#usize
  ok (Array.make 4#usize [a,b,c,d])

theorem replay (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (q : Slice U8) (g : NEV_DotInputs.Coefficients) (domain : NEV_DotInputs.Canonical g) :
    run oracle tailOracle q g=FIp_NativeDots.fast_dots.four_dots q g := by
  simp only [run,FIp_NativeDots.fast_dots.four_dots,
    NFF_FullOne.replay oracle law tailOracle tailLaw _ g domain]

theorem headline (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (q : Slice U8) (g : NEV_DotInputs.Coefficients) (domain : NEV_DotInputs.Canonical g) :
    run oracle tailOracle q g=NEI_FourWrapper.fast_dots.four_dots q g := by
  rw [replay oracle law tailOracle tailLaw q g domain,NEI_FourWrapperLaw.emitted_to_cohort]

#print axioms replay
#print axioms headline
end AspisR1.NFF_FullWrapper
end
