import CurrentClaimScalarReads
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimScalar
open Concrete

theorem chain_return_canonical {D H : Type} {ops : ClaimDotOps D}
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array E 29#usize}
    {point : Usize} {iter : Range} {dot : D} {out : E}
    (trace : Chain ops sem y1 g point iter dot out)
    (hfinish : ∀ state value, ops.finishDot state=Result.ok value → Canonical value) :
    Canonical out := by
  induction trace with
  | done r d x he hf => exact hfinish d x hf
  | step l coeff scalar hn hr hw hp tail ih => exact ih

theorem helper_return_canonical {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize) (out : E)
    (hfinish : ∀ state value, ops.finishDot state=Result.ok value → Canonical value)
    (h : verifier.prepared_claim_dot ops inst sem y1 g point=Result.ok (core.result.Result.Ok out)) :
    Canonical out := by
  obtain ⟨dot,xs,hn,trace,hlen,horder,hreads⟩ := successful_helper_has_exact_reads ops inst sem y1 g point out h
  exact chain_return_canonical trace hfinish

#print axioms chain_return_canonical
#print axioms helper_return_canonical
end AspisR1CurrentPreparedClaim.ClaimScalar
