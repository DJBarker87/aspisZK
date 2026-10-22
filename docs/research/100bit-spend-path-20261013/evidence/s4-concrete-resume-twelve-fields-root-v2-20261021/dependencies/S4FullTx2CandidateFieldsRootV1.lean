import S4Tx2FullSourceOwnedCutV1
import S4Tx2AuthenticatedWrapperCutV1
import S4V10CandidateQueryFieldEvidenceV1
import S4CandidateLoopActualCallsV1
import S4V10CandidateQueryFullWideBoundsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4FullTx2CandidateFieldsRootV1
open AspisR1Stage2
open AspisR1S4Tx2FullSourceOwnedCutV1
open AspisR1S4P6PowersQueryJoinV1
open AspisR1S4CandidateLoopActualCallsV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1
attribute [local irreducible] verifier.candidate.query_loop verifier.candidate.queryWithOps

/-- S4-owned slots are fixed; all other full-body source-cut operations remain explicit. -/
def withS4SourceSlots {H : Type} (ops : Ops H) : Ops H :=
  {ops with split := 10#usize, weightsPowers := sourceP6WeightsPowers}

def candidateCall (aops : AccumulateOps) (rest : QueryOps) :
    AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryCall :=
  fun proof p a g obs geometry pending =>
    verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
      proof p a g obs geometry pending

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B} {x : B}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- The successful source powers result itself supplies the same ClaimPowers
array, without a separately successful prefix or independently chosen g. -/
theorem source_powers_same_claim_array
    (gamma : AspisR1Stage2.aspis_core.field.wide_exact.WideExact)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (hcanonical : AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim gamma))
    (h : sourceP6WeightsPowers 29#usize gamma = .ok g) :
    ∃ powers : ClaimArray,
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
        (stage2ToClaim gamma) = .ok powers ∧
      AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
        AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast powers := by
  unfold sourceP6WeightsPowers at h
  obtain ⟨values,hvalues,hmap⟩ := bind_ok_inv h
  have hpowers := AspisR1PowersP6GeneratedErasureV1.sourceArrayPowers_success_claim
    (stage2ToClaim gamma) hcanonical values hvalues
  refine ⟨values,hpowers,?_⟩
  have hgmap : claimArrayToStage2 values = g := Result.ok.inj hmap
  rw [← hgmap]
  apply Subtype.ext
  change (values.val.map claimToStage2).map
    AspisR1S4FullQueryValuesPrefixV1.fullWideToCurrent =
      values.val.map AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimToFast
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  cases x <;> rfl

/-- Accepted execution of the complete emitted-body cut yields the twelve
actual candidate queries and field-result evidence for their exact callback
outputs. The cursor and powers execution come from that same caller success. -/
theorem full_tx2_source_cut_success_twelve_actual_fields {H : Type}
    (ops : Ops H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (hcanonical : ∀ p a,
      verifier.resumeWithOps ops.resumeOps inst checkpoint proof public_bytes
        transport.Variant.S2 hash = .ok (.Ok (p,a)) →
      AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim p.gamma))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : tx2CommonFullSourceCut (withS4SourceSlots ops) (candidateCall aops rest)
      inst public_bytes proof checkpoint hash obs = .ok (.Ok ())) :
    ∃ (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
      (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (powers : ClaimArray),
      verifier.resumeWithOps ops.resumeOps inst checkpoint proof public_bytes
        transport.Variant.S2 hash = .ok (.Ok (p,a)) ∧
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
        ∃ (q : Slice U8)
          (values : Array AspisR1FastDotsV10CandidateQueryFullWideBoundsV1.FullWide 4#usize),
          AspisR1S4FullQueryValuesPrefixV1.sourceOpening proof a0.next = .ok q ∧
          (concreteCandidateQueryOps rest).dots q g = .ok values ∧
          (∀ x ∈ values.val, AspisR1FastDotsV10CandidateQueryFullWideBoundsV1.FullCoordinateBound x)) := by
  obtain ⟨p,a,g,geometry,pending,aout,bout,hresume,hstart,hpowers,hgeometry,hpending,hloop⟩ :=
    tx2CommonFullSourceCut_success_reaches_query_loop
      (withS4SourceSlots ops) (candidateCall aops rest)
      inst public_bytes proof checkpoint hash obs h
  change verifier.resumeWithOps ops.resumeOps inst checkpoint proof public_bytes
    transport.Variant.S2 hash = .ok (.Ok (p,a)) at hresume
  change a.next = 10#usize at hstart
  change sourceP6WeightsPowers 29#usize p.gamma = .ok g at hpowers
  have hgamma := hcanonical p a hresume
  obtain ⟨powers,hclaim,hcaller⟩ := source_powers_same_claim_array p.gamma g hgamma hpowers
  have hfields := candidate_twelve_queries_have_actual_call_field_results
    aops rest proof p g obs geometry a aout pending bout (stage2ToClaim p.gamma)
    powers hgamma hclaim hcaller hscan (by rw [hstart]; rfl) hloop
  refine ⟨p,a,g,geometry,pending,powers,hresume,hstart,hpowers,hgeometry,hpending,
    hclaim,hcaller,?_⟩
  intro k
  obtain ⟨a0,a1,b0,b1,hindex,hcall,_⟩ := hfields k
  have hevidence := candidate_query_success_field_evidence aops rest proof p a0 g
    obs geometry b0 (.Ok (a1,b1)) (stage2ToClaim p.gamma) powers
    hgamma hclaim hcaller hscan hcall
  obtain ⟨_,_,q,values,hopening,hdots,hbounds⟩ :=
    AspisR1FastDotsV10CandidateQueryFullWideBoundsV1.candidate_query_fullwide_coordinate_bounds
      rest proof p a0 g powers hevidence
  exact ⟨a0,a1,b0,b1,hindex,hcall,hevidence,q,values,hopening,hdots,hbounds⟩

/-- The emitted authenticated wrapper reaches the same complete common body.
This only installs the common-body slot; parseShape and the upstream source
operations remain explicit and are not claimed as concrete implementations. -/
theorem authenticated_source_cut_reaches_full_common {H : Type}
    (ops : Ops H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (parseShape : Slice U8 → Result
      (core.result.Result transport.Variant verifier.Error))
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (h : AspisR1S4Tx2AuthenticatedWrapperCutV1.tx2AuthenticatedOperationCut
      inst parseShape ops.mark
      (tx2CommonFullSourceCut (withS4SourceSlots ops) (candidateCall aops rest))
      public_bytes proof checkpoint hash obs = .ok (.Ok ())) :
    tx2CommonFullSourceCut (withS4SourceSlots ops) (candidateCall aops rest)
      inst public_bytes proof checkpoint hash obs = .ok (.Ok ()) := by
  obtain ⟨_,_,_,hcommon⟩ :=
    AspisR1S4Tx2AuthenticatedWrapperCutV1.accepted_reaches_exact_common
      inst parseShape ops.mark
      (tx2CommonFullSourceCut (withS4SourceSlots ops) (candidateCall aops rest))
      public_bytes proof checkpoint hash obs h
  exact hcommon

#print axioms source_powers_same_claim_array
#print axioms full_tx2_source_cut_success_twelve_actual_fields
#print axioms authenticated_source_cut_reaches_full_common

end AspisR1S4FullTx2CandidateFieldsRootV1
