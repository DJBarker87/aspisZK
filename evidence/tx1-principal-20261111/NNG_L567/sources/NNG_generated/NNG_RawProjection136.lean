import NNG_VerifiedDomain136
import NNG_LIBRecords
import NNG_ArrayTwo136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_RawProjection136
open Aeneas Aeneas.Std NNG_Emitted NNG_Transport NNG_LIBArrays NNG_LIBScalar
open NMT_Transport (arr arr_inverse)

theorem array_raw {n : Usize} (fallback : Value) (a : Array Raw n) (domain : NNG_LIBArrayDomain.DomainArray a) :
 LIB_VScalarCarriers.array LIB_VScalarCarriers.toRaw (projectArray fallback a)=arr toT1 a := by
 have h := congrArg (arr toT1) (NNG_LIBArrayDomain.lower_project_array fallback a domain)
 rw [←NNG_LIBRecords.raise_array,arr_inverse fromT1 toT1 fromT1_inverse] at h
 exact h

theorem claims_raw (fallback : Value) (a : Claims) (domain : NNG_LIBClaimsDomain.DomainClaims a) :
 LIB_VCarriers.claimsRaw (projectClaims fallback a)=arr (arr toT1) a := by
 apply Subtype.ext
 change (a.val.map (projectArray fallback)).map LIB_VCarriers.k29Raw=(a.val.map (arr toT1))
 rw [List.map_map]
 apply List.map_congr_left
 intro row member
 exact array_raw fallback row (domain row member)
#print axioms array_raw
#print axioms claims_raw
end AspisR1.NNG_RawProjection136
