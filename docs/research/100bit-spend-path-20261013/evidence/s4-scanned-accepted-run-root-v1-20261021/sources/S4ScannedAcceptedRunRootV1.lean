import S4ScannedClaimPowersForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsScannedAcceptedRunRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

def bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem four_dots_success_exact_prefix
    (ops : Ops) (q : Slice Std.U8) (g : Array Wide 29#usize)
    (values : Array Wide 4#usize)
    (h : AspisR1FastDotsCurrent.fast_dots.four_dots ops q g = .ok values) :
    ∃ arrayQ : Array Std.U8 608#usize, arrayQ.val = q.val.slice 0 (608#usize) := by
  unfold AspisR1FastDotsCurrent.fast_dots.four_dots at h
  rcases bind_ok_inv h with ⟨slice608, hslice, hrest⟩
  rcases bind_ok_inv hrest with ⟨parsed, hparsed, hrest⟩
  rcases bind_ok_inv hrest with ⟨arrayQ, hunwrap, _harray⟩
  have hsliceBytes : slice608.val = q.val.slice 0 (608#usize) := by
    have hs := hslice
    change core.slice.index.SliceIndexRangeToUsizeSlice.index
      { «end» := 608#usize } q = .ok slice608 at hs
    by_cases hh : (608#usize) ≤ q.length
    · simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index, if_pos hh] at hs
      exact (congrArg (fun s : Slice Std.U8 => s.val) (Result.ok.inj hs)).symm
    · simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index, if_neg hh] at hs
      cases hs
  have hparsedOk : parsed = .Ok arrayQ := by
    cases parsed with
    | Ok actual =>
      have hOk : Result.ok actual = Result.ok arrayQ := by
        simpa only [core.result.Result.unwrap] using hunwrap
      exact congrArg core.result.Result.Ok (Result.ok.inj hOk)
    | Err e =>
      simp only [core.result.Result.unwrap] at hunwrap
      cases hunwrap
  have harrayVal : arrayQ.val = slice608.val := by
    have ht := hparsed
    rw [hparsedOk] at ht
    by_cases hlen : slice608.len = 608#usize
    · simp [core.array.TryFromSharedArraySlice.try_from, hlen] at ht
      exact (congrArg (fun a : Array Std.U8 608#usize => a.val) ht).symm
    · simp [core.array.TryFromSharedArraySlice.try_from, hlen] at ht
  exact ⟨arrayQ, harrayVal.trans hsliceBytes⟩

theorem scanned_accepted_run_literal_values
    (base : Ops) (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (g : Array Wide 29#usize) (values : Array Wide 4#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : g = claimArrayToFast claimPowers)
    (hlen : proof.val.length=57607) (hj : j<22)
    (hread : q.val=proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (hactual : AspisR1FastDotsCurrent.fast_dots.four_dots (install base) q g=.ok values) :
    ∃ (a : Array Std.U8 608#usize) (v0 v1 v2 v3 : Wide),
      a.val=q.val.slice 0 (608#usize) ∧
      (∀ x∈values.val,AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      values.val=[v0,v1,v2,v3] ∧
      LiteralFieldResult (literalOps base) a g 0#usize v0 ∧
      LiteralFieldResult (literalOps base) a g 1#usize v1 ∧
      LiteralFieldResult (literalOps base) a g 2#usize v2 ∧
      LiteralFieldResult (literalOps base) a g 3#usize v3 := by
  obtain ⟨a,ha⟩ := four_dots_success_exact_prefix (install base) q g values hactual
  obtain ⟨computed,v0,v1,v2,v3,hcomputed,hcanonical,hvalues,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsScannedClaimPowersForwardRootV1.four_dots_forward_of_scanner_and_claim_powers
      base proof j q a g gamma claimPowers hgamma hpowers hcaller hlen hj hread hscan ha
  have he : computed=values := Result.ok.inj (hcomputed.symm.trans hactual)
  subst computed
  exact ⟨a,v0,v1,v2,v3,ha,hcanonical,hvalues,h0,h1,h2,h3⟩

#print axioms four_dots_success_exact_prefix
#print axioms scanned_accepted_run_literal_values
end AspisR1FastDotsScannedAcceptedRunRootV1
