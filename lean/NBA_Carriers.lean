import NBA_ClaimCallee
set_option autoImplicit false
namespace AspisR1.NBA_Carriers
open AspisR1ClaimPreparedBridge LPi_FieldValues

def back (x : PE) : NE := LPq_ReadPorts.backE (toClaimE x)

theorem roundtrip (x : PE) : NBA_ClaimCallee.wide (back x)=x := rfl

theorem canonical (x : PE) : canonE (back x) ↔
    AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE x) := Iff.rfl

#print axioms roundtrip
#print axioms canonical
end AspisR1.NBA_Carriers
