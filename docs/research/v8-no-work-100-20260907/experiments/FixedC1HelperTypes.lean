import NearGammaSelectedC1
import ClaimTransport
import ScalarPowerSplit

/-! Diagnostic only: print the literal elaborated summation instances
before trying another concrete specialization. No recovery theorem here. -/
set_option autoImplicit false
set_option maxRecDepth 100
namespace AspisV8.FixedC1HelperTypes
open AspisV8.NearGammaSelectedC1
noncomputable section
def low (claims : Fin 29 → K) (gamma : K) : K :=
  ∑ lane : Fin 26, gamma^lane.val*claims (Fin.castAdd 3 lane)
def high (claims : Fin 29 → K) (gamma : K) : K :=
  ∑ lane : Fin 3, gamma^lane.val*claims (Fin.natAdd 26 lane)
set_option pp.all true in
#print low
set_option pp.all true in
#print high
set_option pp.all true in
#check (ScalarPowerSplit.split (F:=K) 26 3)
end
end AspisV8.FixedC1HelperTypes
