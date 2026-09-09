import SelectedReceivedOracle
import AspisFormal.K1.V7Tag73ExactGRSConversion

/-! Diagnostic only: expose selected versus generic field power instances.
No concrete power, field enumeration or recovery theorem is evaluated. -/
set_option autoImplicit false
namespace AspisV8.CoveredOODGRSTypes
open AspisV8.SelectedReceivedOracle
noncomputable section
def genericPower {F : Type*} [Field F] (x : F) : F := x^512
def selectedPower (x : K) : K := x^512
def selectedGenericPower (x : K) : K := genericPower x
set_option pp.all true in
#print genericPower
set_option pp.all true in
#print selectedPower
set_option pp.all true in
#print selectedGenericPower
set_option pp.all true in
#synth Field K
set_option pp.all true in
#synth Monoid K
set_option pp.all true in
#synth NPow K
end
end AspisV8.CoveredOODGRSTypes
