import RPx_AuditRoot
set_option pp.fullNames true
set_option pp.deepTerms true
set_option format.width 120
#print AspisR1.RPx_Transport.Claims
#print AspisR1.RPx_NativeTransport.PrefixBound
#print AspisR1.F3T_Runtime.StoredCarrierBinding
#print AspisR1.F3T_Runtime.runtimeMass
#check @AspisR1.RPx_Obstruction.arbitrary
#check @AspisR1.RPx_Obstruction.exceeds
#check @AspisR1.RPx_FailedQuery.counted
#check @AspisR1.RPx_RejectMass.runtime
#check @AspisR1.F3T_Numeric.margin_exact
#print axioms AspisR1.RPx_Obstruction.exceeds
#print axioms AspisR1.RPx_AccountCharge.charged
