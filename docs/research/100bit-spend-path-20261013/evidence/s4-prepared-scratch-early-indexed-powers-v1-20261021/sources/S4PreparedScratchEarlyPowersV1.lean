import CurrentPreparedCandidateSamplers
import CurrentPreparedConcreteRun
import S4TenQueryFieldResultsRootV1
import S4TwelveQueryFieldResultsRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4PreparedScratchEarlyPowersV1
open AspisR1CurrentPreparedClaim
open AspisR1ClaimPreparedBridge
open AspisR1PublicPreparation.PreparedScratchReachability
open AspisR1PublicPreparation.PreparedScratchModel
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1

abbrev ClaimE := AspisR1CurrentPreparedClaim.Concrete.E
abbrev FullWide := AspisR1S4FullQueryValuesPrefixV1.FullWide

def claimToFull (x : ClaimE) : FullWide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def claimArrayToFull (xs : Array ClaimE 29#usize) : Array FullWide 29#usize :=
  ⟨xs.val.map claimToFull, by simpa only [List.length_map] using xs.property⟩

theorem claim_array_carrier_to_query_current (xs : Array ClaimE 29#usize) :
    fullArrayToCurrent (claimArrayToFull xs) = claimArrayToFast xs := by
  apply Subtype.ext
  change (xs.val.map claimToFull).map fullWideToCurrent = xs.val.map claimToFast
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  cases x <;> rfl

/-- The early indexed-power candidate is used as the powers field of the
concrete preparation model. This removes the source Std/from_fn seam for this
candidate theorem. The successful preparation run itself supplies both the
powers output and canonical gamma; no independent powers-run premise is used. -/
theorem prepared_success_scratch_is_claim_powers
    {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (scratch scratchIn : Array PE 29#usize)
    (h : prepare (concreteBoundaries (withCandidateSamplers sampling))
      D sem v hash scratchIn = .ok (.Ok out, scratch)) :
    Concrete.Canonical (toClaimE out.gamma) ∧
      ClaimPowers.powers 29#usize (toClaimE out.gamma) =
        .ok (mapArray toClaimE scratch) := by
  have hcan := prepared_candidate_samplers_canonical
    sampling D sem v hash out scratch scratchIn h
  have hrun := prepared_success_concrete_claim
    (withCandidateSamplers sampling) D sem v hash out scratch scratchIn h
  exact ⟨hcan.1, hrun.1⟩

def fullArrayFromPreparedScratch (scratch : Array PE 29#usize) :
    Array FullWide 29#usize := claimArrayToFull (mapArray toClaimE scratch)

abbrev PublicWide := AspisR1PublicPreparation.aspis_core.field.WideExact
abbrev PublicQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev PublicCM := AspisR1PublicPreparation.aspis_core.field.CM31
abbrev PublicCircle := AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint

def publicCMToFull (x : PublicCM) : AspisR1S4FullQueryValuesPrefixV1.FullCM := ⟨x.a, x.b⟩
def publicQMToFull (x : PublicQM) : AspisR1S4FullQueryValuesPrefixV1.FullQM :=
  ⟨publicCMToFull x.c0, publicCMToFull x.c1⟩
def publicWideToFull (x : PublicWide) : FullWide := ⟨publicQMToFull x.c0, publicQMToFull x.c1⟩
def publicCircleToFull (x : PublicCircle) : AspisR1Stage2.aspis_core.circle.SecureCirclePoint :=
  ⟨publicQMToFull x.x, publicQMToFull x.y⟩
def publicVariantToFull (x : AspisR1PublicPreparation.transport.Variant) : AspisR1Stage2.transport.Variant :=
  match x with | .S1 => .S1 | .S2 => .S2 | .D => .D

def publicArrayWideToFull {n : Usize} (xs : Array PublicWide n) : Array FullWide n :=
  ⟨xs.val.map publicWideToFull, by simpa only [List.length_map] using xs.property⟩
def publicArrayQMToFull {n : Usize} (xs : Array PublicQM n) : Array AspisR1S4FullQueryValuesPrefixV1.FullQM n :=
  ⟨xs.val.map publicQMToFull, by simpa only [List.length_map] using xs.property⟩
def publicArrayCircleToFull {n : Usize} (xs : Array PublicCircle n) : Array AspisR1Stage2.aspis_core.circle.SecureCirclePoint n :=
  ⟨xs.val.map publicCircleToFull, by simpa only [List.length_map] using xs.property⟩

def publicPreparedToStage2 (p : AspisR1PublicPreparation.verifier.Prepared) : AspisR1Stage2.verifier.Prepared :=
  { variant := publicVariantToFull p.variant
    roots := p.roots
    gamma := publicWideToFull p.gamma
    kappa := publicWideToFull p.kappa
    alpha := publicArrayWideToFull p.alpha
    rho := publicQMToFull p.rho
    queries := p.queries
    semantic_alpha := publicArrayQMToFull p.semantic_alpha
    z := publicArrayCircleToFull p.z
    claim := publicWideToFull p.claim
    state := p.state }

/-- Ten successful Stage2 queries are proved over the same scratch array
returned by candidate-backed preparation. The early powers loop is a reviewed
candidate implementation; this does not establish equivalence to frozen Rust
Std::array::from_fn or the enclosing tx1 caller. -/
theorem ten_queries_from_prepared_scratch
    {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (prepared : AspisR1PublicPreparation.verifier.Prepared)
    (scratch scratchIn : Array PE 29#usize)
    (hprepared : prepare (concreteBoundaries (withCandidateSamplers sampling))
      D sem v hash scratchIn = .ok (.Ok prepared, scratch))
    (aops : AspisR1Stage2.AccumulateOps)
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops)
    (rest : AspisR1Stage2.QueryOps) (proof : Slice U8)
    (obs : Option (AspisR1Stage2.verifier.Phase → Result Unit))
    (geometry : AspisR1Stage2.verifier.QueryGeometry)
    (a out : AspisR1Stage2.verifier.Accumulator)
    (b bout : AspisR1Stage2.verifier.BatchedWeights)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hstart : a.next.val = 0)
    (hloop : AspisR1Stage2.verifier.candidate.query_loop
      (fun proof p a g obs geometry b => AspisR1Stage2.verifier.candidate.queryWithOps aops
        (AspisR1S4FullQueryValuesPrefixV1.withS4Callbacks
          (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
        proof p a g obs geometry b)
      proof (publicPreparedToStage2 prepared) a (fullArrayFromPreparedScratch scratch)
      obs geometry b 10#usize = .ok (.Ok (out, bout))) :
    ∀ k : Fin 10, ∃ (a0 a1 : AspisR1Stage2.verifier.Accumulator)
      (b0 b1 : AspisR1Stage2.verifier.BatchedWeights),
      a0.next.val = k.val ∧
      AspisR1Stage2.verifier.candidate.queryWithOps aops
        (AspisR1S4FullQueryValuesPrefixV1.withS4Callbacks
          (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
        proof (publicPreparedToStage2 prepared) a0 (fullArrayFromPreparedScratch scratch)
        obs geometry b0 = .ok (.Ok (a1, b1)) ∧
      AspisR1S4TwelveQueryFieldResultsRootV1.QueryFieldEvidence
        headOps proof (publicPreparedToStage2 prepared) (fullArrayFromPreparedScratch scratch) a0 := by
  have hclaim := prepared_success_scratch_is_claim_powers sampling D sem v hash
    prepared scratch scratchIn hprepared
  have hcaller : fullArrayToCurrent (fullArrayFromPreparedScratch scratch) =
      claimArrayToFast (mapArray toClaimE scratch) :=
    claim_array_carrier_to_query_current (mapArray toClaimE scratch)
  exact AspisR1S4TenQueryFieldResultsRootV1.ten_queries_have_field_results
    aops headOps rest proof (publicPreparedToStage2 prepared) (fullArrayFromPreparedScratch scratch)
    obs geometry a out b bout (toClaimE prepared.gamma) (mapArray toClaimE scratch)
    hclaim.1 hclaim.2 hcaller hscan hstart hloop

#print axioms claim_array_carrier_to_query_current
#print axioms prepared_success_scratch_is_claim_powers
#print axioms ten_queries_from_prepared_scratch
end AspisR1S4PreparedScratchEarlyPowersV1
