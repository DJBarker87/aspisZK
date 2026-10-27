import RPz7_CurrentPreparedConcreteRun
import CurrentClaimSourceAggregation
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim AspisR1CurrentPreparedClaim.Concrete
open AspisR1CurrentPreparedClaim.ClaimParts AspisR1S5ClaimDotConcreteAdapter
local notation "QRaw" => AspisR1EbyKPushDecodedProductUpdate.QRaw

def ClaimSourceMeaning {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (inactive gamma kappa out : E) (g : Array E 29#usize) : Prop :=
    ∃ final : Array E 7#usize,
      cell final 0#usize (by scalar_tac)=inactive ∧
      (∀ point : Usize, point.val<6 →
        ∃ (i : Usize) (value : E) (hi : i.val<7),
        ∃ xs : List (Usize × E × aspis_core.field.QM31),
          (point+1#usize : Result Usize)=Result.ok i ∧ cell final i hi=value ∧ xs.length=29 ∧
          (∀ j (hj : j< xs.length), (xs[j]'hj).1.val=j) ∧
          (∀ t ∈ xs, ClaimScalar.SelectedSource sem y1 point t.1 t.2.2 ∧ ClaimScalar.read (concreteOps QRaw) sem y1 point t.1=Result.ok t.2.2 ∧
            Array.index_usize g t.1=Result.ok t.2.1 ∧ decode t.2.1=decode gamma^t.1.val) ∧
          decode value=(xs.map (fun t => decode gamma^t.1.val *
            AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed t.2.2)).sum) ∧
      Canonical out ∧ decode out=kappaPolynomial kappa final

theorem prepared_success_gamma_kappa_source {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (hgamma : Canonical (toClaimE out.gamma))
    (hkappa : Canonical (toClaimE out.kappa))
    (hinactive : Canonical (toClaimE v.inactive))
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries sampling) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ClaimSourceMeaning (toClaimSem sem) v.y1 (toClaimE v.inactive)
      (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim)
      (mapArray toClaimE scratch) := by
  have hr := prepared_success_concrete_claim sampling D sem v hash out scratch scratchIn h
  exact successful_claim_source_gamma_kappa_sum (toClaimDigest D) (toClaimSem sem) v.y1
    (toClaimE v.inactive) (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim)
    (mapArray toClaimE scratch) hgamma hkappa hinactive hr.1 hr.2

#print axioms prepared_success_gamma_kappa_source
end AspisR1ClaimPreparedBridge
