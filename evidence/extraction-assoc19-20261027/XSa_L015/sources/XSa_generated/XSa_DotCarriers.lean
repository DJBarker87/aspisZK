import XSa_ClaimSelect
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSa_DotCarriers
open AspisR1ClaimPreparedBridge
abbrev Dot := XRn_Join_Release.fast_pairing.canonical.Dot
abbrev State := AspisR1S5ClaimDotConcreteAdapter.PushState

def state (a b : Dot) (count : Usize) : State := ⟨⟨a.sums⟩,⟨b.sums⟩,count⟩
def ops := AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw

theorem new_dot : ops.newDot=ok (state XRn_Join_dotZero XRn_Join_dotZero 0#usize) := by
 exact AspisR1FinishDotConcreteOps.sourceNewDot_zero

theorem parser : AspisR1CurrentPreparedClaim.ClaimParser.withParser ops=ops := rfl

#print axioms new_dot
#print axioms parser
#print AspisR1EbyKPushExplicitOpsV1.push
#print AspisR1EbyKPushSourceConversionV1.pushWithSourceCheckedAdd
#print AspisR1EbyKPushSourceConversionV1.pushWithSourceConversion
#print AspisR1QRawGeneratedPushConnectionV2.sourceRawFn
#print AspisR1DotPushLocal.canonical.Dot.push
end XSa_DotCarriers
