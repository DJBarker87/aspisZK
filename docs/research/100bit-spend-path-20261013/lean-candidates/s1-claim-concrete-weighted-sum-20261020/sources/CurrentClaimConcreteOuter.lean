import CurrentClaimKappaPolynomial
import CurrentClaimHelperCanonical
import AspisR1S5ClaimScalarFinishCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimParts
open Concrete AspisR1S5ClaimDotConcreteAdapter

theorem successful_concrete_claim_kappa_polynomial {H : Type}
    (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (inactive kappa out : E) (g : Array E 29#usize)
    (hkappa : Canonical kappa) (hinactive : Canonical inactive)
    (h : verifier.prepared_claim (concreteOps rawFn) inst sem y1 inactive g kappa=
      Result.ok (core.result.Result.Ok out)) :
    ∃ final : Array E 7#usize,
      cell final 0#usize (by scalar_tac)=inactive ∧
      (∀ point : Usize, point.val<6 →
        ∃ (i : Usize) (value : E) (hi : i.val<7),
          (point+1#usize : Result Usize)=Result.ok i ∧
          verifier.prepared_claim_dot (concreteOps rawFn) inst sem y1 g point=
            Result.ok (core.result.Result.Ok value) ∧ cell final i hi=value) ∧
      Canonical out ∧ decode out=kappaPolynomial kappa final := by
  have hops : ClaimPowers.withConcretePowers (concreteOps rawFn)=concreteOps rawFn := rfl
  have hcanon : ∀ point value, point.val<6 →
      verifier.prepared_claim_dot (ClaimPowers.withConcretePowers (concreteOps rawFn)) inst sem y1 g point=
        Result.ok (core.result.Result.Ok value) → Canonical value := by
    intro point value hp hcall
    rw [hops] at hcall
    apply ClaimScalar.helper_return_canonical (concreteOps rawFn) inst sem y1 g point value ?_ hcall
    intro state returned hr
    exact AspisR1S5ClaimScalarFinishCanonical.concrete_finishDot_success_canonical state rawFn returned hr
  obtain ⟨k,final,hpowers,hzero,hvalues,hc,he⟩ := successful_claim_sum_relation
    (concreteOps rawFn) inst sem y1 inactive kappa out g hkappa hinactive hcanon (by simpa only [hops] using h)
  refine ⟨final,hzero,?_,hc,?_⟩
  · simpa only [hops] using hvalues
  · exact he.trans (partialSum_is_kappa_polynomial kappa k final (fun j => (hpowers j).2))

#print axioms successful_concrete_claim_kappa_polynomial
end AspisR1CurrentPreparedClaim.ClaimParts
