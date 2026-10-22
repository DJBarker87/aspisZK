import S4CandidateCallerPreparedRootV1
import S4PrepareInstalledMeaningV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4Tx1InstalledPrepareBridgeV1
open AspisR1CurrentCaller
open AspisR1S4PreparedNewS1AdapterV1
open AspisR1ClaimPreparedBridge
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4CandidatePrepareS1ParentV1
open AspisR1S4CandidateCallerPreparedRootV1

abbrev ClaimE := AspisR1CurrentPreparedClaim.Concrete.E
abbrev CPrepared := AspisR1CurrentCaller.verifier.Prepared
abbrev CWide := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact
abbrev Usize := Std.Usize

def claimToFull (x : ClaimE) : AspisR1Stage2.aspis_core.field.wide_exact.WideExact :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def claimArrayToFull (xs : Array ClaimE 29#usize) :
    Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize :=
  ⟨xs.val.map claimToFull, by simpa only [List.length_map] using xs.property⟩

theorem claim_array_carrier_to_query_current (xs : Array ClaimE 29#usize) :
    fullArrayToCurrent (claimArrayToFull xs) = claimArrayToFast xs := by
  apply Subtype.ext
  change (xs.val.map claimToFull).map fullWideToCurrent = xs.val.map claimToFast
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  cases x with
  | mk c0 c1 =>
    cases c0 with
    | mk c00 c01 =>
      cases c00 with
      | mk a b =>
        cases c01 with
        | mk c d =>
          cases c1 with
          | mk c10 c11 =>
            cases c10 with
            | mk e f =>
              cases c11 with
              | mk g h => rfl

private theorem scratch_stage_eq_claim_full (xs : Array CWide 29#usize) :
    arrayWideToStage xs =
      claimArrayToFull (AspisR1ClaimPreparedBridge.mapArray toClaimE (wArrayToP xs)) := by
  have hpoint : ∀ x : CWide,
      wideToStage x = claimToFull (toClaimE (wToP x)) := by
    intro x
    cases x with
    | mk q0 q1 =>
      cases q0 with
      | mk c00 c01 =>
        cases c00 with
        | mk a b =>
          cases c01 with
          | mk c d =>
            cases q1 with
            | mk c10 c11 =>
              cases c10 with
              | mk e f =>
                cases c11 with
                | mk g h => rfl
  apply Subtype.ext
  simp only [arrayWideToStage, claimArrayToFull,
    AspisR1ClaimPreparedBridge.mapArray, wArrayToP]
  simp only [List.map_map]
  apply List.map_congr_left
  intro x hx
  simpa only [Function.comp] using hpoint x

private theorem scratch_stage_map (xs : Array CWide 29#usize) :
    fullArrayToCurrent (arrayWideToStage xs) =
      claimArrayToFast (AspisR1ClaimPreparedBridge.mapArray toClaimE (wArrayToP xs)) := by
  rw [scratch_stage_eq_claim_full]
  exact claim_array_carrier_to_query_current _

/-- The installed S1 constructor child yields the exact caller/fast-array carrier
identity for the same successful prepare result. -/
theorem prepared_installed_s1_supplies_claim_powers
    {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (ops : Leaves H) (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (g : Array CWide 29#usize) (out : CPrepared) (scratch : Array CWide 29#usize)
    (h : prepareSlot
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      ops d public1 proof hash obs g = .ok (.Ok out, scratch)) :
    ∃ gamma : ClaimE, ∃ powers : Array ClaimE 29#usize,
      ClaimCanonical gamma ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
      fullArrayToCurrent (arrayWideToStage scratch) = claimArrayToFast powers := by
  have hbody : prepareWithS1New
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      ops d public1 proof hash obs g = .ok (.Ok out, scratch) := h
  obtain ⟨hcan, hpow⟩ :=
    AspisR1S4PrepareInstalledMeaningV1.parent_success_installed_meaning
      sampling embed ops d public1 proof hash obs g out scratch hbody
  refine ⟨toClaimE (wToP out.gamma),
    AspisR1ClaimPreparedBridge.mapArray toClaimE (wArrayToP scratch), hcan, hpow, ?_⟩
  exact (scratch_stage_map scratch).trans (congrArg claimArrayToFast rfl)

abbrev COps (H : Type) := AspisR1CallerV4Tx1OpsCut.Ops H
abbrev AccOps := AspisR1Stage2.AccumulateOps
abbrev QOps := AspisR1Stage2.QueryOps
open AspisR1Stage2

/-- Install the source-shaped parent plus accepted S1 constructor adapter into
    the preparation slot of the tx1 operation record. Other fields are preserved. -/
def withInstalledPrepare {H : Type} (ops : COps H)
    (B : AspisR1PublicPreparation.PreparedScratchModel.Boundaries)
    (leaves : Leaves H) : COps H :=
  { ops with prepare := prepareSlot B leaves }

/-- A successful tx1 call under the S1-installed preparation slot yields the
    same-run gamma, powers, Stage2/Current array map, scan acceptance, and ten
    query-loop result. No separate preparation-binding hypothesis is needed. -/
theorem source_caller_reaches_prepared_loop_installed
    {H : Type}
    (ops : COps H) (aops : AccOps) (rest : QOps)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (leaves : Leaves H)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice Std.U8) (k : Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : alloc.vec.Vec Std.U8)
    (filled : Usize → AspisR1CurrentCaller.aspis_core.field.QM31 →
      Result (core.result.Result (alloc.vec.Vec AspisR1CurrentCaller.aspis_core.field.QM31)
        AspisR1CurrentCaller.aspis_core.r0.Error))
    (hscanBinding : (withInstalledPrepare ops
        (AspisR1ClaimPreparedBridge.concreteBoundaries
          (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
        leaves).canonicalScan proof = .ok (.Ok ()) →
      MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      (AspisR1S4CandidateCallerPreparedRootV1.sourceCaller
        (withInstalledPrepare ops
          (AspisR1ClaimPreparedBridge.concreteBoundaries
            (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
          leaves)
        aops rest filled)
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = 10#usize ∧ ∃ (p : CPrepared) (g : Array CWide 29#usize)
      (a : AspisR1CurrentCaller.verifier.Accumulator)
      (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
      (b : AspisR1CurrentCaller.verifier.BatchedWeights)
      (outS : AspisR1Stage2.verifier.Accumulator) (boutS : AspisR1Stage2.verifier.BatchedWeights)
      (gamma : ClaimE) (powers : Array ClaimE 29#usize),
      (∃ zero : CWide, (withInstalledPrepare ops
        (AspisR1ClaimPreparedBridge.concreteBoundaries
          (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
        leaves).prepare inst public1 proof hash obs (Array.repeat 29#usize zero) = .ok (.Ok p,g)) ∧
      ClaimCanonical gamma ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
      fullArrayToCurrent (arrayWideToStage g) = claimArrayToFast powers ∧
      MultiproofParserRef.parser_reference.scan proof = .ok true ∧
      a.next = 0#usize ∧
      verifier.candidate.query_loop
        (AspisR1S4CandidateCallerPreparedRootV1.candidateCall aops rest) proof
        (preparedToStage p) (accumulatorToStage a) (arrayWideToStage g)
        (obs.map (fun f => fun phase => f (phaseToCaller phase)))
        (geometryToStage geometry) (batchedWeightsToStage b) 10#usize = .ok (.Ok (outS,boutS)) := by
  let opsI := withInstalledPrepare ops
    (AspisR1ClaimPreparedBridge.concreteBoundaries
      (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed)) leaves
  obtain ⟨hk,p,g,a,geometry,b,outS,boutS,hscan,⟨zero,hprep⟩,hstart,hloop⟩ :=
    AspisR1S4CandidateCallerPreparedRootV1.source_caller_reaches_ten_loop
      opsI aops rest inst public1 public_bytes proof k hash obs bytes filled h
  obtain ⟨gamma,powers,hcanonical,hpowers,harray⟩ :=
    prepared_installed_s1_supplies_claim_powers sampling embed leaves inst public1 proof hash obs
      (Array.repeat 29#usize zero) p g hprep
  refine ⟨hk,p,g,a,geometry,b,outS,boutS,gamma,powers,⟨zero,hprep⟩,
    hcanonical,hpowers,harray,hscanBinding hscan,hstart,?_⟩
  simpa only [hk] using hloop

#print axioms source_caller_reaches_prepared_loop_installed
end AspisR1S4Tx1InstalledPrepareBridgeV1
