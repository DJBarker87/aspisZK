import S4OriginalPortQueryOpsTotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1.S4OriginalPortAcceptedQueryV1

open AspisR1Stage2
open AspisR1FastDotsV10QueryOpsResultTransportV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1.MixedLeafEncoding AspisR1.MixedLeafDecoder

private theorem index_success_bound {α : Type} {n : Usize}
    (xs : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize xs i = .ok x) : i.val < n.val := by
  have hlen : i.val < xs.val.length := by
    by_contra hnot
    have hnone : xs[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [xs.property] using hlen

/-- A successful complete source-shaped query reaches the same original-port
dot outputs whose four mathematical batches are derived here. The continuation
after dots remains the complete queryWithOps body; no V10 execution is used.
Library and caller installation of this named port remain unproved here. -/
theorem successful_query_has_exact_original_port_batches
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (acc : verifier.Accumulator)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (out : core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
    (gamma : ClaimE) (powers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers)
    (hcaller : fullArrayToCurrent g = claimArrayToFast powers)
    (hlen : proof.val.length = 57607)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hquery : verifier.candidate.queryWithOps aops (withOldModelDots concreteOps rest)
      proof p acc g obs geometry pending = .ok out) :
    ∃ (i : U32) (u : Usize) (q : Slice U8) (dots : Array FullWide 4#usize)
      (a : Array U8 608#usize) (c1 : C1) (c2 : C2),
      Array.index_usize p.queries acc.next = .ok i ∧
      lift (UScalar.cast .Usize i) = .ok u ∧
      sourceOpening proof acc.next = .ok q ∧
      (withOldModelDots concreteOps rest).dots q g = .ok dots ∧
      a.val = q.val.slice 0 (608#usize) ∧
      decodeC1 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480) = some c1 ∧
      decodeC2 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480) = some c2 ∧
      dots.val.map (fun x => AspisR1CurrentPreparedClaim.Concrete.decode
        (AspisR1S4P6PowersQueryJoinV1.stage2ToClaim x)) =
        List.ofFn (fun slot : Fin 4 => AspisV6Width29CorrelatedAgreement.width29Batch
          (AspisR1D18S4ConcreteWidth29KernelV1.localWord c1 c2 slot)
          (AspisR1CurrentPreparedClaim.Concrete.decode gamma)) := by
  obtain ⟨i,u,q,dots,hi,hu,hopening,hdots⟩ :=
    full_query_values_success_prefix aops (withOldModelDots concreteOps rest)
      proof p acc g obs geometry pending out hquery
  have hopening' : sourceOpening proof acc.next = .ok q := by
    simpa [withOldModelDots] using hopening
  have hj : acc.next.val < 22 := by
    simpa using index_success_bound p.queries acc.next i hi
  obtain ⟨q',hq',hread'⟩ :=
    AspisR1S4OpeningBytesFromCurrentV1.opening_slice_exact
      proof acc.next hj (by omega : 28359 ≤ proof.val.length)
  have hqeq : q' = q := Result.ok.inj (hq'.symm.trans hopening')
  have hread : q.val = proof.val.slice
      (10055+acc.next.val*832) (10055+acc.next.val*832+832) := by
    simpa [hqeq] using hread'
  obtain ⟨values,a,c1,c2,hvalues,ha,hd1,hd2,hmeaning⟩ :=
    S4OriginalPortQueryOpsTotalV1.original_port_queryops_dots_total_exact_batches
      rest proof acc.next.val q g gamma powers hgamma hpowers hcaller hlen hj hread hscan
  have heq : values = dots := Result.ok.inj (hvalues.symm.trans hdots)
  subst values
  exact ⟨i,u,q,dots,a,c1,c2,hi,hu,hopening',hdots,ha,hd1,hd2,hmeaning⟩

#print axioms successful_query_has_exact_original_port_batches

end AspisR1.S4OriginalPortAcceptedQueryV1
