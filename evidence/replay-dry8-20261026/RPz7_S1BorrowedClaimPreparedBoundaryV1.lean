import S1ClaimBorrowedAbiTransportV1
import RPz7_CurrentOriginalPreparedInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim

/-- Exact borrowed reference child, using the concrete early-return powers,
field, dot and trace interpretation already selected by concreteOps.
Original native whole-call correspondence is a separate obligation. -/
def claim {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : PE) (g : Array PE 29#usize) (kappa : PE) :
    Result (core.result.Result PE AspisR1PublicPreparation.verifier.Error) := do
  let r ← verifier.borrowed_abi.prepared_claim_owned
    (AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw)
    (toClaimDigest D) (toClaimSem sem) y1 (toClaimE inactive)
    (mapArray toClaimE g) (toClaimE kappa)
  ok (match r with | .Ok x => .Ok (fromClaimE x) | .Err e => .Err (fromClaimError e))

theorem claim_eq {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : PE) (g : Array PE 29#usize) (kappa : PE) :
    claim D sem y1 inactive g kappa = claimPublic D sem y1 inactive g kappa := by
  unfold claim claimPublic
  rw [BorrowedAbiTransport.borrowed_claim_eq_source]
  rfl

def boundaries (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    AspisR1PublicPreparation.PreparedScratchModel.Boundaries :=
  {sampling:=sampling,powers:=powersPublic,claim:=claim}

theorem boundaries_eq (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    boundaries sampling=concreteBoundaries sampling := by
  have hc : @claim = @claimPublic := by
    funext H D sem y1 inactive g kappa
    exact claim_eq D sem y1 inactive g kappa
  unfold boundaries concreteBoundaries
  rw [hc]

/-- Original Prepared.new body with the borrowed reference and early-return
powers installed. Complete Result and scratch are retained on both errors. -/
def originalNew (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :=
  OriginalPreparedSource.prepare (boundaries (installedBoundaries sampling embed)) D sem v hash g

theorem originalNew_eq_transport
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    originalNew sampling embed D sem v hash g =
    (do
      let (r,scratch) ← AspisR1PublicPreparation.PreparedScratchModel.prepare
        (concreteBoundaries (installedBoundaries sampling embed))
        (InstalledPreparation.retainedDigest D) (InstalledPreparation.retainedSem sem)
        (InstalledPreparation.retainedView v) hash (mapArray InstalledPreparation.retainedE g)
      ok ((match r with | .Ok x => .Ok (InstalledPreparation.currentPrepared x)
                        | .Err e => .Err (InstalledPreparation.currentError e)),
          mapArray InstalledPreparation.currentE scratch)) := by
  unfold originalNew
  rw [boundaries_eq,OriginalPreparedSource.prepare_transport]
  unfold OriginalPreparedSource.transported
  rw [AspisR1PublicPreparation.OriginalPreparedNative.eq_prepare]
  rfl

#print axioms claim_eq
#print axioms boundaries_eq
#print axioms originalNew_eq_transport
end AspisR1CurrentCaller.BorrowedClaimPrepared
