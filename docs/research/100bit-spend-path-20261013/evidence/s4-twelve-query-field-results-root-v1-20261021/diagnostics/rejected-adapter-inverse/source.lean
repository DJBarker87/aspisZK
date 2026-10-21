import S4FullQueryValuesPrefixV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1Stage2
open AspisR1S4FullQueryValuesPrefixV1

/-- The full field witness returned by the successful actual query body. -/
def QueryFieldEvidence
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops)
    (proof : Slice U8) (p : verifier.Prepared)
    (g : Array FullWide 29#usize) (a : verifier.Accumulator) : Prop :=
∃ (i : U32) (u : Usize) (q : Slice U8)
      (dots : Array CurrentWide 4#usize)
      (arrayQ : Array U8 608#usize) (v0 v1 v2 v3 : CurrentWide),
      Array.index_usize p.queries a.next = .ok i ∧
      lift (UScalar.cast .Usize i) = .ok u ∧
      sourceOpening proof a.next = .ok q ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots
        (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) q
        (fullArrayToCurrent g) = .ok dots ∧
      arrayQ.val = q.val.slice 0 (608#usize) ∧
      (∀ x ∈ dots.val, AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      dots.val = [v0,v1,v2,v3] ∧
      AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
        (AspisR1FastDotsForwardLiteralValueRootV1.literalOps headOps)
        arrayQ (fullArrayToCurrent g) 0#usize v0 ∧
      AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
        (AspisR1FastDotsForwardLiteralValueRootV1.literalOps headOps)
        arrayQ (fullArrayToCurrent g) 1#usize v1 ∧
      AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
        (AspisR1FastDotsForwardLiteralValueRootV1.literalOps headOps)
        arrayQ (fullArrayToCurrent g) 2#usize v2 ∧
      AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
        (AspisR1FastDotsForwardLiteralValueRootV1.literalOps headOps)
        arrayQ (fullArrayToCurrent g) 3#usize v3

private theorem adapted_ok_inv {A B E : Type}
    (call : Stage2ContinuationOwnedLoop.Call A B E) (a a1 : A) (b b1 : B)
    (h : Stage2ContinuationOwnedLoop.adapt call a b = .ok (.Ok (),a1,b1)) :
    call a b = .ok (.Ok (a1,b1)) := by
  unfold Stage2ContinuationOwnedLoop.adapt at h
  cases hc : call a b with
  | fail e => simp [hc] at h
  | div => simp [hc] at h
  | ok r =>
    cases r with
    | Err e => simp [hc] at h
    | Ok pair =>
      rcases pair with ⟨a2,b2⟩
      have hp : a2=a1 ∧ b2=b1 := by simpa [hc] using h
      rcases hp with ⟨rfl,rfl⟩
      exact hc

/-- Locate each actual call in the ordered source chain. -/
theorem chain_call_at {A B E : Type} (next : A → Nat)
    (call : Stage2ContinuationLoop.Call A B E)
    (advance : ∀ a a1 b b1, call a b = .ok (.Ok (),a1,b1) → next a1=next a+1)
    {a out : A} {b bout : B} {n : Nat}
    (hchain : Stage2ContinuationLoop.Chain next call a b out bout n) :
    ∀ k : Nat, k<n → ∃ a0 a1 b0 b1,
      next a0=next a+k ∧ call a0 b0=.ok (.Ok (),a1,b1) := by
  induction hchain with
  | done a b atEnd => intro k hk; omega
  | @step a a1 out b b1 bout n active hc tail ih =>
    intro k hk
    cases k with
    | zero => exact ⟨a,a1,b,b1,by omega,hc⟩
    | succ k =>
      obtain ⟨a0,a2,b0,b2,hnext,hcall⟩ := ih k (by omega)
      have hstep := advance a a1 b b1 hc
      exact ⟨a0,a2,b0,b2,by omega,hcall⟩

/-- Every one of the twelve queries of a successful complete stage-2 source
loop supplies the field witnesses, not merely an independently assumed query. -/
theorem twelve_queries_have_field_results
    (aops : AccumulateOps) (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops)
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (gamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE)
    (claimPowers : Array AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE 29#usize)
    (hgamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma=.ok claimPowers)
    (hcaller : fullArrayToCurrent g=AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers)
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (hstart : a.next.val=10)
    (hloop : verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
        proof p a g obs geometry b)
      proof p a g obs geometry b 22#usize=.ok (.Ok (out,bout))) :
    ∀ k : Fin 12, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
      a0.next.val=10+k.val ∧
      verifier.candidate.queryWithOps aops
        (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
        proof p a0 g obs geometry b0=.ok (.Ok (a1,b1)) ∧
      QueryFieldEvidence headOps proof p g a0 := by
  let ops := withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest
  let call : QueryCall := fun proof p a g obs geometry b =>
    verifier.candidate.queryWithOps aops ops proof p a g obs geometry b
  have advance : ∀ a a1 b b1, call proof p a g obs geometry b=.ok (.Ok (a1,b1)) →
      a1.next.val=a.next.val+1 := by
    intro a a1 b b1 hc
    exact query_next aops ops proof p a a1 g obs geometry b b1 hc
  have chain := emitted_twelve_ordered_calls call proof p g obs geometry advance
    a out b bout hstart hloop
  intro k
  have hadv : ∀ a a1 b b1,
      Stage2ContinuationOwnedLoop.adapt (fun a b => call proof p a g obs geometry b) a b =
        .ok (.Ok (),a1,b1) → a1.next.val=a.next.val+1 := by
    intro a a1 b b1 hc
    exact advance a a1 b b1 (adapted_ok_inv _ a a1 b b1 hc)
  obtain ⟨a0,a1,b0,b1,hindex,hcall⟩ := chain_call_at _ _ hadv chain k.val k.isLt
  have hc := adapted_ok_inv _ a0 a1 b0 b1 hcall
  refine ⟨a0,a1,b0,b1,by omega,hc,?_⟩
  exact full_query_values_success_scanned_field_results aops headOps rest proof p a0 g obs
    geometry b0 (.Ok (a1,b1)) gamma claimPowers hgamma hpowers hcaller hscan hc

#print axioms chain_call_at
#print axioms twelve_queries_have_field_results
end AspisR1S4TwelveQueryFieldResultsRootV1
