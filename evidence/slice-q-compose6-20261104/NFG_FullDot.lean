import NFF_FullOne
import NFF_Primitive
import NFG_Primitive64
import NFE_WrapperBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_FullDot
open Aeneas Aeneas.Std Result
/-- The native logged program with both primitive reply laws discharged in Lean. -/
def one (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) :=
 NFF_FullOne.run NFF_Primitive.reply NFG_Primitive64.reply q g slot

theorem one_result (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
 (canonical : NEV_DotInputs.Canonical g) (slot : Usize) :
 one q g slot=FIp_NativeDots.fast_dots.four_dots_one q g slot :=
 NFF_FullOne.replay NFF_Primitive.reply NFF_Primitive.law
  NFG_Primitive64.reply NFG_Primitive64.law q g canonical slot

def four (q : Slice U8) (g : NEV_DotInputs.Coefficients) :
 Result (Array NEV_DotCarrier.NE 4#usize) := do
 let window ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) q {«end»:=608#usize}
 let converted ← core.array.TryFromSharedArraySlice.try_from 608#usize window
 let fixed ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted
 let a ← one fixed g 0#usize
 let b ← one fixed g 1#usize
 let c ← one fixed g 2#usize
 let d ← one fixed g 3#usize
 ok (Array.make 4#usize [a,b,c,d])

theorem four_result (q : Slice U8) (g : NEV_DotInputs.Coefficients)
 (canonical : NEV_DotInputs.Canonical g) :
 four q g=FIp_NativeDots.fast_dots.four_dots q g := by
 simp only [four,FIp_NativeDots.fast_dots.four_dots,one_result _ g canonical]

theorem headline (q : Slice U8) (g : NEV_DotInputs.Coefficients)
 (canonical : NEV_DotInputs.Canonical g) :
 four q g=NEI_FourWrapper.fast_dots.four_dots q g := by
 rw [four_result q g canonical,NEI_FourWrapperLaw.emitted_to_cohort]
#print axioms one_result
#print axioms four_result
#print axioms headline
end AspisR1.NFG_FullDot
end
