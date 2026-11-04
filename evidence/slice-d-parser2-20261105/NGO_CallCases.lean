import NGO_CallerDomains
set_option autoImplicit false
namespace NGO_CallCases
/-- Native K014/K015 checks the original u8 cast/add for these ten steps. -/
theorem round (i : Nat) (live : i<10) :
    NGO_CallerDomains.Call (15+i) 28 0 :=
  NGO_CallerDomains.Call.round (15+i) (by omega) (by omega)
/-- Native K016/K017 checks the original usize multiplication. -/
theorem claims (p : Nat) (live : p<3) : NGO_CallerDomains.Call 25 29 (p*29) :=
  NGO_CallerDomains.Call.claims p live
#print axioms round
#print axioms claims
end NGO_CallCases
