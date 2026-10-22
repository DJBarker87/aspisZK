import S4P6PowersQueryJoinV1
import S4TwelveQueryFieldResultsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4Tx2PrefixTwelveFieldResultsRootV1
open AspisR1Stage2
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1S4P6PowersQueryJoinV1

/-- The complete tx2 prefix supplies the actual same coefficient array and
successful query loop. No powers-success, coefficient-array equality or
individual query-success premise is independently supplied. -/
theorem tx2_prefix_twelve_field_results {H : Type}
    (ops : ClaimOps H) (aops : AccumulateOps)
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (bout : verifier.BatchedWeights) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (hgamma : AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim p.gamma))
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (hstart : a.next.val=10)
    (h : AspisR1FastDotsTx2PowersQuerySourceCutV1.tx2QueryPrefix
      (withSourceP6WeightsPowers ops)
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
        proof p a g obs geometry b)
      proof p a hash obs=.ok (.Ok (out,bout))) :
    ∃ g : Array FullWide 29#usize,
      sourceP6WeightsPowers 29#usize p.gamma=.ok g ∧
      ∃ geometry : verifier.QueryGeometry,
      (withSourceP6WeightsPowers ops).makeGeometry p.queries a.next 22#usize=.ok geometry ∧
      ∀ k : Fin 12, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val=10+k.val ∧
        verifier.candidate.queryWithOps aops
          (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
          proof p a0 g obs
          geometry b0
          =.ok (.Ok (a1,b1)) ∧
        QueryFieldEvidence headOps proof p g a0 := by
  obtain ⟨g,hg,geometry,hgeometry,pending,hpending,hloop,claimPowers,hpowers,hcaller⟩ :=
    tx2_prefix_p6_powers_same_g ops _ proof p a hash obs (.Ok (out,bout)) hgamma h
  refine ⟨g,hg,geometry,hgeometry,?_⟩
  exact twelve_queries_have_field_results aops headOps rest proof p g obs geometry
    a out pending bout (stage2ToClaim p.gamma) claimPowers hgamma hpowers hcaller
    hscan hstart hloop

#print axioms tx2_prefix_twelve_field_results
end AspisR1S4Tx2PrefixTwelveFieldResultsRootV1
