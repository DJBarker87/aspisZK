import Stage2ContinuationQueryAdvance
import AspisR1FastDotsCurrent.FunsOpsV4
import R22Stage2LocalBodies
import S4OpeningBytesFromCurrentV1
import S4ScannedOpeningForwardRootV1
import S4ScannedAcceptedRunRootV1
import FourDotsClaimPowerCoordinateBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4FullQueryValuesPrefixV1

open AspisR1Stage2

abbrev FullWide := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev FullQM := AspisR1Stage2.aspis_core.field.QM31
abbrev FullCM := AspisR1Stage2.aspis_core.field.CM31
abbrev CurrentWide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev CurrentQM := AspisR1FastDotsCurrent.aspis_core.field.QM31
abbrev CurrentCM := AspisR1FastDotsCurrent.aspis_core.field.CM31

def fullCMToCurrent (x : FullCM) : CurrentCM :=
  ⟨x.a, x.b⟩

def fullQMToCurrent (x : FullQM) : CurrentQM :=
  ⟨fullCMToCurrent x.c0, fullCMToCurrent x.c1⟩

def fullWideToCurrent (x : FullWide) : CurrentWide :=
  ⟨fullQMToCurrent x.c0, fullQMToCurrent x.c1⟩

def currentCMToFull (x : CurrentCM) : FullCM := ⟨x.a, x.b⟩
def currentQMToFull (x : CurrentQM) : FullQM :=
  ⟨currentCMToFull x.c0, currentCMToFull x.c1⟩
def currentWideToFull (x : CurrentWide) : FullWide :=
  ⟨currentQMToFull x.c0, currentQMToFull x.c1⟩

def fullArrayToCurrent {n : Usize} (xs : Array FullWide n) : Array CurrentWide n :=
  ⟨xs.val.map fullWideToCurrent, by simpa only [List.length_map] using xs.property⟩

def currentArrayToFull {n : Usize} (xs : Array CurrentWide n) : Array FullWide n :=
  ⟨xs.val.map currentWideToFull, by simpa only [List.length_map] using xs.property⟩

def sourceOpening : Slice U8 → Usize → Result (Slice U8) :=
  fun proof index => AspisR1Stage2.verifier.candidate.opening proof index

def withS4Callbacks
    (base : AspisR1FastDotsCurrent.FourDotsOps)
    (rest : QueryOps) : QueryOps :=
  { rest with
    opening := sourceOpening
    dots := fun q g => do
      let dots ← AspisR1FastDotsCurrent.fast_dots.four_dots base q
        (fullArrayToCurrent g)
      ok (currentArrayToFull dots) }

private theorem result_bind_ok_inv {α β : Type} {r : Result α}
    {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- Success of the complete emitted query-values operation sequence implies
    success of its first four source operations.  The body after `dots` is
    retained inside `queryWithOps`; this theorem only inverts its successful
    Result binds and does not substitute a cut continuation. -/
theorem full_query_values_success_prefix
    (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (out : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
      verifier.Error)
    (h : verifier.candidate.queryWithOps aops ops proof p a g obs geometry pending =
      .ok out) :
    ∃ (i : U32) (u : Usize) (q : Slice U8)
      (dots : Array Stage2E 4#usize),
      Array.index_usize p.queries a.next = .ok i ∧
      lift (UScalar.cast .Usize i) = .ok u ∧
      ops.opening proof a.next = .ok q ∧
      ops.dots q g = .ok dots := by
  unfold verifier.candidate.queryWithOps at h
  obtain ⟨i, hi, h⟩ := result_bind_ok_inv h
  obtain ⟨u, hu, h⟩ := result_bind_ok_inv h
  obtain ⟨q, hq, h⟩ := result_bind_ok_inv h
  obtain ⟨dots, hdots, _⟩ := result_bind_ok_inv h
  exact ⟨i, u, q, dots, hi, hu, hq, hdots⟩

/-- The full source-shaped query body, with its existing tail still present,
    reaches the same opening and current S4 `four_dots` calls consumed by the
    S4 prefix proof.  Only the generated backend operation record is
    parameterized; all operations after `dots` remain in `queryWithOps`. -/
theorem full_query_values_success_current_s4
    (aops : AccumulateOps) (base : AspisR1FastDotsCurrent.FourDotsOps)
    (rest : QueryOps) (proof : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (out : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
      verifier.Error)
    (h : verifier.candidate.queryWithOps aops (withS4Callbacks base rest)
      proof p a g obs geometry pending = .ok out) :
    ∃ (i : U32) (u : Usize) (q : Slice U8)
      (dots : Array CurrentWide 4#usize),
      Array.index_usize p.queries a.next = .ok i ∧
      lift (UScalar.cast .Usize i) = .ok u ∧
      sourceOpening proof a.next = .ok q ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots base q
        (fullArrayToCurrent g) = .ok dots := by
  obtain ⟨i,u,q,dotsFull,hi,hu,hopening,hdots⟩ :=
    full_query_values_success_prefix aops (withS4Callbacks base rest)
      proof p a g obs geometry pending out h
  have hopening' : sourceOpening proof a.next = .ok q := by
    simpa [withS4Callbacks] using hopening
  unfold withS4Callbacks at hdots
  obtain ⟨dots, hcurrent, hmap⟩ := result_bind_ok_inv hdots
  have hmap' : currentArrayToFull dots = dotsFull := Result.ok.inj hmap
  have hback : fullArrayToCurrent (currentArrayToFull dots) = dots := by
    cases dots with
    | mk values hlen => simp [fullArrayToCurrent, currentArrayToFull,
        fullWideToCurrent, currentWideToFull, fullQMToCurrent,
        currentQMToFull, fullCMToCurrent, currentCMToFull,
        List.map_map, Function.comp_def]
  have hdot : AspisR1FastDotsCurrent.fast_dots.four_dots base q
      (fullArrayToCurrent g) = .ok (fullArrayToCurrent dotsFull) := by
    have hout : dots = fullArrayToCurrent dotsFull := by
      calc
        dots = fullArrayToCurrent (currentArrayToFull dots) := hback.symm
        _ = fullArrayToCurrent dotsFull := congrArg fullArrayToCurrent hmap'
    exact hcurrent.trans (congrArg Result.ok hout)
  exact ⟨i,u,q,fullArrayToCurrent dotsFull,hi,hu,hopening',hdot⟩

private theorem query_index_success_bound {α : Type} {n : Usize}
    (xs : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize xs i = .ok x) : i.val < n.val := by
  have hlen : i.val < xs.val.length := by
    by_contra hnot
    have hnone : xs[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [xs.property] using hlen

private theorem scanned_proof_length (proof : Slice U8)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    proof.val.length = 57607 := by
  have hlen : Slice.len proof = 57607#usize := by
    by_cases hlen : Slice.len proof = 57607#usize
    · exact hlen
    · have hneq : (Slice.len proof != 57607#usize) = true := by simp [hlen]
      have hfalse : MultiproofParserRef.parser_reference.scan proof = .ok false := by
        simp [MultiproofParserRef.parser_reference.scan, hneq]
      rw [hfalse] at hscan
      cases hscan
  have hv := congrArg UScalar.val hlen
  simpa [Slice.len, Slice.length] using hv

/-- A successful full source-shaped query, with the actual R22 opening reader
and installed current four-dot backend, carries the strict-scanner-derived
literal field meaning for the very same returned four-dot array. The whole
`queryWithOps` continuation remains in the success hypothesis; only the
backend operations are selected through their existing source-owner record. -/
theorem full_query_values_success_scanned_field_results
    (aops : AccumulateOps)
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops)
    (rest : QueryOps) (proof : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (out : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
      verifier.Error)
    (gamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE)
    (claimPowers : Array AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE 29#usize)
    (hgamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : fullArrayToCurrent g =
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : verifier.candidate.queryWithOps aops
      (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
      proof p a g obs geometry pending = .ok out) :
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
        arrayQ (fullArrayToCurrent g) 3#usize v3 := by
  obtain ⟨i,u,q,dots,hi,hu,hopening,hdots⟩ :=
    full_query_values_success_current_s4 aops
      (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest
      proof p a g obs geometry pending out h
  have hj : a.next.val < 22 := by
    have hi' := query_index_success_bound p.queries a.next i hi
    simpa using hi'
  have hlen := scanned_proof_length proof hscan
  obtain ⟨q', hq', hread'⟩ :=
    AspisR1S4OpeningBytesFromCurrentV1.opening_slice_exact proof a.next
      hj (by omega : 28359 ≤ proof.val.length)
  have hqeq : q' = q := Result.ok.inj (hq'.symm.trans hopening)
  have hread : q.val = proof.val.slice
      (10055 + a.next.val * 832) (10055 + a.next.val * 832 + 832) := by
    simpa [hqeq] using hread'
  obtain ⟨arrayQ, harrayQ⟩ :=
    AspisR1FastDotsScannedAcceptedRunRootV1.four_dots_success_exact_prefix
      (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) q
      (fullArrayToCurrent g) dots hdots
  have hcoordsBase :=
    AspisR1FastDotsClaimPowerCoordinateBridgeV1.actual_fastdots_coordinate_bounds_of_claim_powers
      (fullArrayToCurrent g) gamma claimPowers hgamma hpowers hcaller
  have hcoords : ∀ j : Fin 29,
      AspisR1FastDotsHeadTailSharedWitnessRootV2.CoordBound
        ((fullArrayToCurrent g).val[j.val]'(by
          simpa [fullArrayToCurrent, g.property] using j.isLt)) := by
    intro j
    change AspisR1FastDotsWideLimbCanonical.CoordinateBound
      ((fullArrayToCurrent g).val[j.val]'(by
        simpa [fullArrayToCurrent, g.property] using j.isLt))
    exact hcoordsBase j
  obtain ⟨values,v0,v1,v2,v3,hactual,hcanonical,hvalues,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsScannedOpeningForwardRootV1.four_dots_forward_of_scanned_opening
      headOps proof a.next.val q arrayQ (fullArrayToCurrent g)
      hlen (by omega) hread hscan harrayQ hcoords
  have hvaluesEq : values = dots := Result.ok.inj (hactual.symm.trans hdots)
  subst values
  exact ⟨i,u,q,dots,arrayQ,v0,v1,v2,v3,hi,hu,hopening,hdots,harrayQ,
    hcanonical,hvalues,h0,h1,h2,h3⟩

#print axioms result_bind_ok_inv
#print axioms full_query_values_success_prefix
#print axioms full_query_values_success_current_s4
#print axioms full_query_values_success_scanned_field_results

end AspisR1S4FullQueryValuesPrefixV1
