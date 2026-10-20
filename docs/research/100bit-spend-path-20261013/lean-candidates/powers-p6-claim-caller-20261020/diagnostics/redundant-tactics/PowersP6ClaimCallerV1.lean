import PowersP6ClaimAgreementV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PowersP6ClaimCallerV1
open AspisR1CurrentPreparedClaim AspisR1PowersP6ClaimAgreementV1
open AspisR1CurrentPreparedClaim.Concrete

def withSourcePowers {D : Type} (ops : ClaimDotOps D) : ClaimDotOps D :=
  {ops with powers := sourceModelPowers}

/-- The nested claim loop never consults the powers operation. -/
theorem claim_loop_powers_irrelevant {D H : Type} (ops : ClaimDotOps D)
    (p q : (N : Usize) → E → Result (Array E N))
    (inst : aspis_core.Digest32 H) (iter : core.ops.range.Range Usize)
    (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array E 29#usize) (k parts : Array E 7#usize) :
    verifier.prepared_claim_loop {ops with powers := p} inst iter sem y1 g k parts =
    verifier.prepared_claim_loop {ops with powers := q} inst iter sem y1 g k parts := by
  rfl

/-- Replacing only powers preserves the entire claim result, including errors
and divergence, on canonical kappa. The source/P6 interface remains explicit. -/
theorem prepared_claim_sourcePowers_eq {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (inactive : E) (g : Array E 29#usize) (kappa : E)
    (hk : Canonical kappa) :
    verifier.prepared_claim (withSourcePowers ops) inst sem y1 inactive g kappa =
    verifier.prepared_claim (ClaimPowers.withConcretePowers ops) inst sem y1 inactive g kappa := by
  unfold verifier.prepared_claim
  change (do let k ← sourceModelPowers 7#usize kappa; _) =
    (do let k ← ClaimPowers.powers 7#usize kappa; _)
  rw [sourceModelPowers_eq_claimPowers 7#usize kappa hk]
  congr 1
  funext k
  congr 1
  funext parts
  exact claim_loop_powers_irrelevant ops sourceModelPowers ClaimPowers.powers inst _ sem y1 g k parts

#print axioms claim_loop_powers_irrelevant
#print axioms prepared_claim_sourcePowers_eq
end AspisR1PowersP6ClaimCallerV1
