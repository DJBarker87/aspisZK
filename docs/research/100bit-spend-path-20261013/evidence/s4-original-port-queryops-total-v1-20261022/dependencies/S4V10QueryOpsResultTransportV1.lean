import S4FullQueryValuesPrefixV1
import S4V10LiteralOuterTransferRootV1
import S4WholeOuterTransferRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsV10QueryOpsResultTransportV1

open AspisR1S4FullQueryValuesPrefixV1
open AspisR1Stage2
open AspisR1FastDotsV10CarrierMapV1
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1S4FourWrapperCarrierTransportRootV1 (mapArray)
open AspisR1FastDotsV10LiteralOuterTransferRootV1 (literalV10Outer)

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact

/-- Convert the exact query coefficients to the V10 carrier by the inverse of
the existing transparent V10→Current map. -/
def fullArrayToV10 {n : Usize} (xs : Array FullWide n) : Array V10Wide n :=
  ⟨xs.val.map (fun x => wideFromEbyK (fullWideToCurrent x)),
    by simpa only [List.length_map] using xs.property⟩

theorem fullArrayToV10_map (xs : Array FullWide 29#usize) :
    mapWideArray (fullArrayToV10 xs) = fullArrayToCurrent xs := by
  apply Subtype.ext
  simp only [mapWideArray, fullArrayToV10, fullArrayToCurrent,
    List.map_map, Function.comp_def]
  simp only [wide_roundtrip']

/-- Candidate QueryOps four-dot callback: preserve the same q and query g,
run the literal V10 outer, then map its returned values into the query carrier. -/
def literalDots (base : Ops) (q : Slice U8) (g : Array FullWide 29#usize) :
    Result (Array FullWide 4#usize) := do
  let values ← literalV10Outer
    (AspisR1FastDotsFourCallbacksForwardRootV1.install base) q (fullArrayToV10 g)
  ok (currentArrayToFull (mapArray wideToEbyK values))

def withLiteralDots (base : Ops) (rest : QueryOps) : QueryOps :=
  { rest with
    opening := sourceOpening
    dots := fun q g => literalDots base q g }

private theorem bind_ok_inv {α β : Type} {r : Result α}
    {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Every successful candidate QueryOps dots call transfers to the original
P6-model callback on the same q and g, with the exact same returned FullWide
array. The candidate's accepted result supplies success; no independent
success or source-runtime correspondence is assumed here. -/
theorem literal_dots_success_eq_current
    (base : Ops) (q : Slice U8) (g : Array FullWide 29#usize)
    (values : Array FullWide 4#usize)
    (hcall : literalDots base q g = .ok values) :
    (do
      let out ← AspisR1FastDotsCurrent.fast_dots.four_dots
        (AspisR1FastDotsFourCallbacksForwardRootV1.install base) q
        (fullArrayToCurrent g)
      ok (currentArrayToFull out)) = .ok values := by
  unfold literalDots at hcall
  obtain ⟨literalValues, hliteral, hvalues⟩ := bind_ok_inv hcall
  have hfixed :=
    AspisR1FastDotsV10LiteralOuterTransferRootV1.literal_outer_success_current
      (AspisR1FastDotsFourCallbacksForwardRootV1.install base) q
      (fullArrayToV10 g) literalValues hliteral
  have hold :=
    AspisR1FastDotsWholeOuterTransferRootV1.installed_fixed_four_success_old_four
      base q (mapWideArray (fullArrayToV10 g))
      (mapArray wideToEbyK literalValues) hfixed
  have hinput : mapWideArray (fullArrayToV10 g) = fullArrayToCurrent g :=
    fullArrayToV10_map g
  rw [hinput] at hold
  have hvalues' : currentArrayToFull (mapArray wideToEbyK literalValues) = values :=
    Result.ok.inj hvalues
  rw [hold]
  simp only [bind_tc_ok, hvalues']


/-- Success of the complete query using the candidate callback supplies the
actual opening and candidate dots success. That reached candidate result is
then transported to the old P6 callback on the same query/coefficient input.
All other query operations and the continuation remain the source-shaped
`queryWithOps`; this theorem is a one-way accepted-run refinement at the dots
site, not equality of the complete query results. -/
theorem successful_query_candidate_dots_transfers
    (aops : AccumulateOps) (base : Ops) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (out : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
      verifier.Error)
    (h : verifier.candidate.queryWithOps aops (withLiteralDots base rest)
      proof p a g obs geometry pending = .ok out) :
    ∃ (i : U32) (u : Usize) (q : Slice U8)
      (dots : Array FullWide 4#usize),
      Array.index_usize p.queries a.next = .ok i ∧
      lift (UScalar.cast .Usize i) = .ok u ∧
      sourceOpening proof a.next = .ok q ∧
      literalDots base q g = .ok dots ∧
      (do
        let current ← AspisR1FastDotsCurrent.fast_dots.four_dots
          (AspisR1FastDotsFourCallbacksForwardRootV1.install base) q
          (fullArrayToCurrent g)
        ok (currentArrayToFull current)) = .ok dots := by
  obtain ⟨i,u,q,dots,hi,hu,hopening,hdots⟩ :=
    full_query_values_success_prefix aops (withLiteralDots base rest)
      proof p a g obs geometry pending out h
  have hopening' : sourceOpening proof a.next = .ok q := by
    simpa [withLiteralDots] using hopening
  have hdots' : literalDots base q g = .ok dots := by
    change literalDots base q g = .ok dots at hdots
    exact hdots
  exact ⟨i,u,q,dots,hi,hu,hopening',hdots',
    literal_dots_success_eq_current base q g dots hdots'⟩


/-- The old P6 callback lifted to the FullWide query carrier. -/
def oldModelDots (base : Ops) (q : Slice U8)
    (g : Array FullWide 29#usize) : Result (Array FullWide 4#usize) := do
  let current ← AspisR1FastDotsCurrent.fast_dots.four_dots
    (AspisR1FastDotsFourCallbacksForwardRootV1.install base) q
    (fullArrayToCurrent g)
  ok (currentArrayToFull current)

def withOldModelDots (base : Ops) (rest : QueryOps) : QueryOps :=
  { rest with
    opening := sourceOpening
    dots := fun q g => oldModelDots base q g }

/-- A successful full query using the candidate callback is accepted by the
same source-shaped `queryWithOps` with the old P6 callback, returning the exact
same complete query result. The proof changes only the reached dots result;
the source continuation after dots is shared literally. -/
theorem successful_query_candidate_refines_old_model
    (aops : AccumulateOps) (base : Ops) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (out : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
      verifier.Error)
    (h : verifier.candidate.queryWithOps aops (withLiteralDots base rest)
      proof p a g obs geometry pending = .ok out) :
    verifier.candidate.queryWithOps aops (withOldModelDots base rest)
      proof p a g obs geometry pending = .ok out := by
  unfold verifier.candidate.queryWithOps at h
  obtain ⟨i,hi,h⟩ := bind_ok_inv h
  obtain ⟨u,hu,h⟩ := bind_ok_inv h
  obtain ⟨q,hopening,h⟩ := bind_ok_inv h
  obtain ⟨dots,hdots,hrest⟩ := bind_ok_inv h
  have hopening' : sourceOpening proof a.next = .ok q := by
    simpa [withLiteralDots] using hopening
  have hcurrent : oldModelDots base q g = .ok dots :=
    literal_dots_success_eq_current base q g dots (by
      change literalDots base q g = .ok dots
      exact hdots)
  unfold verifier.candidate.queryWithOps
  simp only [withOldModelDots, hi, hu, hopening', hcurrent, bind_tc_ok]
  exact hrest

#print axioms fullArrayToV10_map
#print axioms literal_dots_success_eq_current
#print axioms successful_query_candidate_dots_transfers
#print axioms successful_query_candidate_refines_old_model

end AspisR1FastDotsV10QueryOpsResultTransportV1
