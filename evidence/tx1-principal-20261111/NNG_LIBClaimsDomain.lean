import NNG_LIBClaims
import NNG_LIBArrayDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBClaimsDomain
open Aeneas Aeneas.Std Result NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays NNG_LIBArrayDomain
open AspisR1.NMT_Transport (arr)
def DomainClaims (claims : Claims) : Prop := ∀ row ∈ claims.val,DomainArray row

theorem lower_canonical (claims : LIB_VCarriers.Claims) : DomainClaims (lowerClaims claims) := by
  intro row member
  obtain ⟨a,_,same⟩ := List.mem_map.mp member
  subst row
  exact NNG_LIBArrayDomain.lower_canonical a
#print axioms lower_canonical

theorem lower_project (fallback : Value) (claims : Claims) (domain : DomainClaims claims) :
    lowerClaims (projectClaims fallback claims) = claims := by
  apply Subtype.ext
  change (claims.val.map (projectArray fallback)).map lowerArray = claims.val
  rw [List.map_map]
  calc
    claims.val.map (lowerArray ∘ projectArray fallback) = claims.val.map id := by
      apply List.map_congr_left
      intro row member
      exact lower_project_array fallback row (domain row member)
    _ = claims.val := List.map_id _
#print axioms lower_project

theorem returned (env : RSL.Env) (p : LIB_VCarriers.Prefix) (claims : Claims)
    (success : NNG_LIBClaims.call env (fromT12 (LIB_VCarriers.prefixRaw p)) = .ok (.Ok claims)) :
    DomainClaims claims := by
  have whole := NNG_LIBClaims.call_model env p
  rw [success] at whole
  cases h : env.reservation with
  | false => simp only [h,Bool.false_eq_true,if_false] at whole;cases whole
  | true =>
    simp only [h,if_true] at whole
    have same := core.result.Result.Ok.inj (Result.ok.inj whole)
    rw [same]
    exact lower_canonical _
#print axioms returned
end AspisR1.NNG_LIBClaimsDomain
