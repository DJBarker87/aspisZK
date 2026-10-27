import XRy_ClaimAdd
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRy_ClaimFold
open AspisR1ClaimPreparedBridge

def canonicalList (xs : List C.E) : Prop := ∀ x ∈ xs, XRy_WideMultiply.Canonical x

theorem fold (pairs : List (C.E × C.E))
 (hc : ∀ pair ∈ pairs, XRy_WideMultiply.Canonical pair.1 ∧ XRy_WideMultiply.Canonical pair.2)
 (sum : C.E) (hs : XRy_WideMultiply.Canonical sum) :
 ∃ out, XRy_WideMultiply.Canonical out ∧
 pairs.foldlM (fun sum pair => do
   let term ← aspis_core.field.wide_exact.WideExact.mul pair.1 pair.2
   aspis_core.field.wide_exact.WideExact.add sum term) sum = ok out ∧
 pairs.foldlM (fun sum pair => do
   let term ← AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul
     (toClaimE pair.1) (toClaimE pair.2)
   AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add sum term) (toClaimE sum) =
   ok (toClaimE out) := by
 induction pairs generalizing sum with
 | nil => exact ⟨sum,hs,rfl,rfl⟩
 | cons pair rest ih =>
   have hp := hc pair (by simp)
   obtain ⟨term,et,ht,tt⟩ := XRy_ClaimArithmetic.multiply pair.1 pair.2 hp.1 hp.2
   obtain ⟨next,en,hn,tn⟩ := XRy_ClaimAdd.add sum term hs ht
   obtain ⟨out,ho,er,tr⟩ := ih (fun p h => hc p (List.mem_cons_of_mem pair h)) next hn
   refine ⟨out,ho,?_,?_⟩
   · simp only [List.foldlM_cons,et,en,bind_tc_ok]
     exact er
   · simp only [List.foldlM_cons,tt,tn,bind_tc_ok]
     exact tr

#print axioms fold
end XRy_ClaimFold
