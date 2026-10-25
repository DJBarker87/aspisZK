import S1ClaimAcceptedCellsV1
import S1BorrowedClaimPreparedBoundaryV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS1ClaimAcceptedCallerRanges
open AspisR1ClaimPreparedBridge AspisS1ClaimAcceptedScalarRanges

/-- Predicate on the SAME complete current semantic return, through the
existing full-field retained/claim maps. All87 input cells are covered. -/
def CurrentClaimsNumeric {H : Type} (sem : AspisR1CurrentCaller.r1_semantic.Verified H) : Prop :=
  ClaimsCanonical (toClaimSem (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem))

/-- The existing borrowed ABI/source equality and concrete checked-Q guards
derive Claims ranges from acceptance. No Claims-producer range/success premise. -/
theorem borrowed_claim_cells_canonical {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive kappa out : PE) (g : Array PE 29#usize)
    (hk : AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE kappa))
    (accepted : AspisR1CurrentCaller.BorrowedClaimPrepared.claim D sem y1 inactive g kappa = ok (.Ok out)) :
    ClaimsCanonical (toClaimSem sem) := by
  rw [AspisR1CurrentCaller.BorrowedClaimPrepared.claim_eq] at accepted
  have called := claimPublic_success D sem y1 inactive kappa out g accepted
  exact accepted_claim_cells_canonical AspisR1EbyKPushDecodedProductUpdate.QRaw
    (toClaimDigest D) (toClaimSem sem) y1 (toClaimE inactive) (toClaimE kappa)
    (toClaimE out) (mapArray toClaimE g) hk called

#print axioms borrowed_claim_cells_canonical
end AspisS1ClaimAcceptedCallerRanges
