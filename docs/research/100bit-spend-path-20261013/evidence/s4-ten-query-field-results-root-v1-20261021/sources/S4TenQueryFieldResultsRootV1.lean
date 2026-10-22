import S4TwelveQueryFieldResultsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S4TenQueryFieldResultsRootV1
open AspisR1Stage2
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1

private theorem shifted_body (call : QueryCall) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry) :
    verifier.candidate.query_loop_loop.body call proof p g obs geometry 10#usize =
      Stage2ContinuationOwnedLoop.body (fun a : verifier.Accumulator => a.next.val+12)
        (fun a b => call proof p a g obs geometry b) := by
  funext state
  cases state with
  | Err e => rfl
  | Ok pair =>
    rcases pair with ⟨a,b⟩
    change (if 10 ≤ a.next.val then _ else _) = (if 22 ≤ a.next.val+12 then _ else _)
    by_cases h : 10 ≤ a.next.val
    · have hs : 22 ≤ a.next.val+12 := by omega
      simp only [if_pos h, if_pos hs]
    · have hs : ¬22 ≤ a.next.val+12 := by omega
      simp only [if_neg h, if_neg hs]

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
      rfl

/-- Reuse the existing symbolic 22-end loop theorem with a +12 cursor
shift; the emitted end10 source body is unchanged. This avoids replaying
or normalizing a concrete ten-step recurrence. -/
theorem emitted_ten_ordered_calls (call : QueryCall) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (advance : ∀ a a1 b b1, call proof p a g obs geometry b=.ok (.Ok (a1,b1)) →
      a1.next.val=a.next.val+1)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (start : a.next.val=0)
    (h : verifier.candidate.query_loop call proof p a g obs geometry b 10#usize =
      .ok (.Ok (out,bout))) :
    Stage2ContinuationLoop.Chain (fun a : verifier.Accumulator => a.next.val+12)
      (Stage2ContinuationOwnedLoop.adapt (fun a b => call proof p a g obs geometry b))
      a b out bout 10 := by
  have hadv : ∀ a a1 b b1, call proof p a g obs geometry b=.ok (.Ok (a1,b1)) →
      a1.next.val+12=(a.next.val+12)+1 := by
    intro a a1 b b1 hc
    have := advance a a1 b b1 hc
    omega
  have hrun : Stage2ContinuationOwnedLoop.run
      (fun a : verifier.Accumulator => a.next.val+12)
      (fun a b => call proof p a g obs geometry b) a b = .ok (.Ok (out,bout)) := by
    simpa only [verifier.candidate.query_loop,verifier.candidate.query_loop_loop,
      shifted_body,Stage2ContinuationOwnedLoop.run] using h
  have chain := Stage2ContinuationOwnedLoop.successful_loop_chain
    (fun a : verifier.Accumulator => a.next.val+12)
    (fun a b => call proof p a g obs geometry b) hadv a out b bout
    (by omega) hrun
  simpa only [start] using chain

theorem ten_queries_have_field_results
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
    (hstart : a.next.val=0)
    (hloop : verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
        proof p a g obs geometry b)
      proof p a g obs geometry b 10#usize=.ok (.Ok (out,bout))) :
    ∀ k : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
      a0.next.val=k.val ∧
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
  have chain := emitted_ten_ordered_calls call proof p g obs geometry advance
    a out b bout hstart hloop
  intro k
  have hadv : ∀ a a1 b b1,
      Stage2ContinuationOwnedLoop.adapt (fun a b => call proof p a g obs geometry b) a b =
        .ok (.Ok (),a1,b1) → a1.next.val+12=(a.next.val+12)+1 := by
    intro a a1 b b1 hc
    have := advance a a1 b b1 (adapted_ok_inv _ a a1 b b1 hc)
    omega
  obtain ⟨a0,a1,b0,b1,hindex,hcall⟩ := chain_call_at _ _ hadv chain k.val k.isLt
  have hc := adapted_ok_inv _ a0 a1 b0 b1 hcall
  refine ⟨a0,a1,b0,b1,by omega,hc,?_⟩
  exact full_query_values_success_scanned_field_results aops headOps rest proof p a0 g obs
    geometry b0 (.Ok (a1,b1)) gamma claimPowers hgamma hpowers hcaller hscan hc


#print axioms ten_queries_have_field_results
#print axioms shifted_body
#print axioms emitted_ten_ordered_calls
end AspisR1S4TenQueryFieldResultsRootV1
