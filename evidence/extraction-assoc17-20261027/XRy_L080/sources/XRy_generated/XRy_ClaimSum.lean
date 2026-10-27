import XRy_ClaimSumLoop
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRy_ClaimSumStep
set_option autoImplicit false
namespace XRy_ClaimSum
open AspisR1ClaimPreparedBridge

theorem zero_canonical : XRy_WideMultiply.Canonical XRy_Powers.zero := by
 constructor <;> constructor <;> constructor <;> decide

theorem zero_claim : toClaimE XRy_Powers.zero =
 AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.ZERO := by
 unfold AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.ZERO
 rfl

theorem sum (k parts : Seven) (hk : canonical k) (hp : canonical parts) :
 ∃ out, XRy_WideMultiply.Canonical out ∧
 XRy_ClaimSumLoop.run k parts 7 0#usize XRy_Powers.zero=ok out ∧
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_sum (arr toClaimE k) (arr toClaimE parts) =
   ok (toClaimE out) := by
 obtain ⟨out,ho,hr,ht⟩ := XRy_ClaimSumLoop.paired 7 k parts hk hp
   ⟨0#usize,7#usize⟩ XRy_Powers.zero zero_canonical (by scalar_tac) (by scalar_tac)
 refine ⟨out,ho,hr,?_⟩
 unfold AspisR1CurrentPreparedClaim.verifier.prepared_claim_sum
 rw [←zero_claim,ht,bind_tc_ok]
 simp only [AspisR1CurrentPreparedClaim.trace.value,bind_tc_ok]

#print axioms zero_canonical
#print axioms zero_claim
#print axioms sum
end XRy_ClaimSum
