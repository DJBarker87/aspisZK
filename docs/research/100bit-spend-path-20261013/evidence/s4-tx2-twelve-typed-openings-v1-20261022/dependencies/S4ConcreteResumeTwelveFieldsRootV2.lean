import S4FullTx2CandidateFieldsRootV1
import S4ResumeGammaActualCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4ConcreteResumeTwelveFieldsRootV2
open AspisR1Stage2
open AspisR1S4P6PowersQueryJoinV1
open AspisR1FastDotsV10CandidateQueryFullWideBoundsV1

/-- Raw decoder-coordinate bounds imply the exact canonical coefficient
contract already used by the S4 powers and query proofs. The map changes
only type owners; no field operation or decoder is interpreted here. -/
theorem raw_bounds_claim_canonical
    (x : AspisR1Stage2.aspis_core.field.wide_exact.WideExact)
    (h : FullCoordinateBound x) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim x) := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  change ((x.c0.c0.a.val < 2147483647 ∧ x.c0.c0.b.val < 2147483647) ∧
    (x.c0.c1.a.val < 2147483647 ∧ x.c0.c1.b.val < 2147483647)) ∧
    ((x.c1.c0.a.val < 2147483647 ∧ x.c1.c0.b.val < 2147483647) ∧
    (x.c1.c1.a.val < 2147483647 ∧ x.c1.c1.b.val < 2147483647))
  exact ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩

open AspisR1S4Tx2FullSourceOwnedCutV1
open AspisR1S4FullTx2CandidateFieldsRootV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1
attribute [local irreducible] verifier.candidate.query_loop verifier.candidate.queryWithOps

def withConcreteResume {H : Type} (ops : Ops H) : Ops H :=
  {ops with resumeOps := AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops.resumeOps}

/-- Accepted complete settlement execution with the source Reader.e installed
supplies its own gamma canonicality. Prior same-proof strict scan remains an
explicit two-transaction input-context contract. -/
theorem full_tx2_concrete_reader_twelve_actual_fields {H : Type}
    (ops : Ops H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : tx2CommonFullSourceCut (withS4SourceSlots (withConcreteResume ops))
      (candidateCall aops rest) inst public_bytes proof checkpoint hash obs = .ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator)
      (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (powers : ClaimArray),
      verifier.resumeWithOps (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops.resumeOps)
        inst checkpoint proof public_bytes transport.Variant.S2 hash = .ok (.Ok (p,a)) ∧
      a.next = 10#usize ∧
      sourceP6WeightsPowers 29#usize p.gamma = .ok g ∧
      ops.forRange p.queries a.next 22#usize = .ok (.Ok geometry) ∧
      ops.newPending (alloc.vec.Vec.deref a.weights) = .ok (.Ok pending) ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
        (stage2ToClaim p.gamma) = .ok powers ∧
      AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
        AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast powers ∧
      (∀ k : Fin 12, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = 10+k.val ∧
        candidateCall aops rest proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
        CandidateQueryFieldEvidence rest proof p a0 g powers ∧
        ∃ (q : Slice U8) (values : Array FullWide 4#usize),
          AspisR1S4FullQueryValuesPrefixV1.sourceOpening proof a0.next = .ok q ∧
          (concreteCandidateQueryOps rest).dots q g = .ok values ∧
          (∀ x ∈ values.val, FullCoordinateBound x)) := by
  apply full_tx2_source_cut_success_twelve_actual_fields
    (withConcreteResume ops) aops rest inst public_bytes proof checkpoint hash obs
    (hscan := hscan) (h := h)
  intro p a hresume
  have hraw := AspisR1S4ResumeGammaActualCanonicalV1.resume_gamma_canonical
    ops.resumeOps inst checkpoint proof public_bytes transport.Variant.S2 hash p a hresume
  exact raw_bounds_claim_canonical p.gamma hraw

#print axioms raw_bounds_claim_canonical
#print axioms full_tx2_concrete_reader_twelve_actual_fields
end AspisR1S4ConcreteResumeTwelveFieldsRootV2
