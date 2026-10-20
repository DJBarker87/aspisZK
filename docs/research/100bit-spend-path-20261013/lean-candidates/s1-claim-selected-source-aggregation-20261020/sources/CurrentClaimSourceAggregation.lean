import CurrentClaimGammaScalarSum
import CurrentClaimSelectedScalarSource
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimParts
open Concrete AspisR1S5ClaimDotConcreteAdapter
local notation "QRaw" => AspisR1EbyKPushDecodedProductUpdate.QRaw

theorem successful_claim_source_gamma_kappa_sum {H : Type}
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
          (∀ t ∈ xs, ClaimScalar.SelectedSource sem y1 point t.1 t.2.2 ∧ ClaimScalar.read (concreteOps QRaw) sem y1 point t.1=Result.ok t.2.2 ∧
            Array.index_usize g t.1=Result.ok t.2.1 ∧ decode t.2.1=decode gamma^t.1.val) ∧
          decode value=(xs.map (fun t => decode gamma^t.1.val *
            AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed t.2.2)).sum) ∧
      Canonical out ∧ decode out=kappaPolynomial kappa final := by
  obtain ⟨final,hzero,hvalues,hout,he⟩ := successful_claim_gamma_kappa_scalar_sum
    inst sem y1 inactive gamma kappa out g hgamma hkappa hinactive hg h
  refine ⟨final,hzero,?_,hout,he⟩
  intro point hp
  obtain ⟨i,value,hi,xs,hinc,hcell,hlen,horder,hreads,hdecode⟩ := hvalues point hp
  refine ⟨i,value,hi,xs,hinc,hcell,hlen,horder,?_,hdecode⟩
  intro t ht
  exact ⟨ClaimScalar.successful_concrete_read_selected_source QRaw sem y1 point t.1 t.2.2
    (hreads t ht).1,hreads t ht⟩

#print axioms successful_claim_source_gamma_kappa_sum
end AspisR1CurrentPreparedClaim.ClaimParts
