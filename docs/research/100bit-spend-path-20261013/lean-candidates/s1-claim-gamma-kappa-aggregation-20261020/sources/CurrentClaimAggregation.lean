import CurrentClaimConcreteOuter
import CurrentClaimPowerReads
import AspisR1S5ClaimScalarConcreteQRawTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimParts
open Concrete AspisR1S5ClaimDotConcreteAdapter
local notation "QRaw" => AspisR1EbyKPushDecodedProductUpdate.QRaw

theorem successful_claim_gamma_kappa_aggregation {H : Type}
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (inactive gamma kappa out : E) (g : Array E 29#usize)
    (hgamma : Canonical gamma) (hkappa : Canonical kappa) (hinactive : Canonical inactive)
    (hg : ClaimPowers.powers 29#usize gamma=Result.ok g)
    (h : verifier.prepared_claim (concreteOps QRaw) inst sem y1 inactive g kappa=
      Result.ok (core.result.Result.Ok out)) :
    ∃ final : Array E 7#usize,
      cell final 0#usize (by scalar_tac)=inactive ∧
      (∀ point : Usize, point.val<6 →
        ∃ (i : Usize) (value : E) (hi : i.val<7),
        ∃ xs : List (Usize × E × aspis_core.field.QM31),
          (point+1#usize : Result Usize)=Result.ok i ∧ cell final i hi=value ∧ xs.length=29 ∧
          (∀ j (hj : j< xs.length), (xs[j]'hj).1.val=j) ∧
          (∀ t ∈ xs, ClaimScalar.read (concreteOps QRaw) sem y1 point t.1=Result.ok t.2.2 ∧
            Array.index_usize g t.1=Result.ok t.2.1 ∧ decode t.2.1=decode gamma^t.1.val) ∧
          decode value=AspisR1FinishDotReturnedFieldProductV1.productSum
            (AspisR1S5ClaimScalarConcreteQRawTrace.finishRows xs)) ∧
      Canonical out ∧ decode out=kappaPolynomial kappa final := by
  have hweights : ∀ i value, Array.index_usize g i=Result.ok value → Canonical value := by
    intro i value hr
    exact (ClaimPowers.powers_success_read gamma g hgamma hg i value hr).1
  obtain ⟨final,hzero,hvalues,hout,he⟩ := successful_concrete_claim_kappa_polynomial
    QRaw inst sem y1 inactive kappa out g hkappa hinactive h
  refine ⟨final,hzero,?_,hout,he⟩
  intro point hp
  obtain ⟨i,value,hi,hinc,hcall,hcell⟩ := hvalues point hp
  obtain ⟨xs,hlen,horder,hreads,hdecode⟩ :=
    AspisR1S5ClaimScalarConcreteQRawTrace.successful_concrete_claim_dot_decoded_product_sum
      inst sem y1 g point value hweights hcall
  refine ⟨i,value,hi,xs,hinc,hcell,hlen,horder,?_,hdecode⟩
  intro t ht
  obtain ⟨hr,hw⟩ := hreads t ht
  exact ⟨hr,hw,(ClaimPowers.powers_success_read gamma g hgamma hg t.1 t.2.1 hw).2⟩

#print axioms successful_claim_gamma_kappa_aggregation
end AspisR1CurrentPreparedClaim.ClaimParts
