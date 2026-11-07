import NNG_LIBClaimsDomain
import NNG_ProjectionFallback137
import LIB_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_VerifiedDomain136
open Aeneas Aeneas.Std NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBArrayDomain NNG_LIBClaimsDomain

/-- Exactly the raw scalar fields retained in the returned semantic record.
This is a local intermediate invariant, not a new RowSpec input clause. -/
structure Canonical (v : r1_semantic.Verified Unit) : Prop where
 challenges : ∃ c : LIB_VCarriers.Challenges, v.challenges=NNG_LIBArrays.lowerChallenges c
 alpha : DomainArray v.alpha
 claims : DomainClaims v.claims
 extra : DomainArray v.extra
 beforeZ1 : DomainArray v.before_z1

end AspisR1.NNG_VerifiedDomain136
