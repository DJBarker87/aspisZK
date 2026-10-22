import FourDotsClaimPowerCoordinateBridgeV1
import S4TailFieldProductRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4ClaimPowersSemanticV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1FastDotsTailFieldProductRootV1

theorem claimToFast_decode (x : ClaimE) :
    wideDecoded (claimToFast x) = AspisR1CurrentPreparedClaim.Concrete.decode x := by
  rfl

/-- Exact coefficients of the same successful powers call, not a fresh
independently chosen power array. -/
theorem successful_powers_exact (gamma : ClaimE) (powers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers) :
    ∀ j : Fin 29,
      wideDecoded ((claimArrayToFast powers).val[j.val]'(by scalar_tac)) =
        AspisR1CurrentPreparedClaim.Concrete.decode gamma ^ j.val := by
  obtain ⟨out,hout,hexact⟩ :=
    AspisR1CurrentPreparedClaim.ClaimPowers.powers_total_exact 29#usize gamma hgamma
  have heq : out = powers := Result.ok.inj (hout.symm.trans hpowers)
  subst powers
  intro j
  simpa only [claimArrayToFast, List.getElem_map, claimToFast_decode] using (hexact j).2

theorem caller_powers_exact (g : Array FastWide 29#usize) (gamma : ClaimE)
    (powers : Array ClaimE 29#usize) (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers)
    (hcaller : g = claimArrayToFast powers) :
    ∀ j : Fin 29, wideDecoded (g.val[j.val]'(by scalar_tac)) =
      AspisR1CurrentPreparedClaim.Concrete.decode gamma ^ j.val := by
  subst g
  exact successful_powers_exact gamma powers hgamma hpowers
#print axioms claimToFast_decode
#print axioms successful_powers_exact
#print axioms caller_powers_exact
end AspisR1.S4ClaimPowersSemanticV1
