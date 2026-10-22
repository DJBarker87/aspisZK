import S4Tx1InstalledPrepareBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4Tx1ActualGammaBridgeV1
open AspisR1CurrentCaller
open AspisR1S4PreparedNewS1AdapterV1
open AspisR1ClaimPreparedBridge
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4CandidatePrepareS1ParentV1
open AspisR1S4Tx1InstalledPrepareBridgeV1

abbrev ClaimE := AspisR1CurrentPreparedClaim.Concrete.E
abbrev CWide := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact

def claimToFull (x : ClaimE) : AspisR1Stage2.aspis_core.field.wide_exact.WideExact :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def claimArrayToFull (xs : Array ClaimE 29#usize) :
    Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize :=
  ⟨xs.val.map claimToFull, by simpa only [List.length_map] using xs.property⟩

private theorem claim_array_carrier_to_query_current (xs : Array ClaimE 29#usize) :
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

private theorem scratch_stage_map (xs : Array CWide 29#usize) :
    fullArrayToCurrent (arrayWideToStage xs) =
      claimArrayToFast (AspisR1ClaimPreparedBridge.mapArray toClaimE (wArrayToP xs)) := by
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
  have harray : arrayWideToStage xs =
      claimArrayToFull (AspisR1ClaimPreparedBridge.mapArray toClaimE (wArrayToP xs)) := by
    apply Subtype.ext
    simp only [arrayWideToStage, claimArrayToFull,
      AspisR1ClaimPreparedBridge.mapArray, wArrayToP]
    simp only [List.map_map]
    apply List.map_congr_left
    intro x hx
    simpa only [Function.comp] using hpoint x
  rw [harray]
  exact claim_array_carrier_to_query_current _

/-- For the exact same successful installed preparation call, expose the returned
    Prepared gamma itself (rather than an existentially named gamma), its
    canonicality and successful ClaimPowers result, and the carrier map of the
    returned scratch array. -/
theorem actual_prepared_gamma_meaning {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (leaves : Leaves H) (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (g scratch : Array CWide 29#usize) (p : CPrepared)
    (hprep : prepareSlot
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      leaves d public1 proof hash obs g = .ok (.Ok p, scratch)) :
    ClaimCanonical (toClaimE (wToP p.gamma)) ∧
    AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
      (toClaimE (wToP p.gamma)) = .ok
        (AspisR1ClaimPreparedBridge.mapArray toClaimE (wArrayToP scratch)) ∧
    fullArrayToCurrent (arrayWideToStage scratch) =
      claimArrayToFast (AspisR1ClaimPreparedBridge.mapArray toClaimE (wArrayToP scratch)) := by
  have hbody : prepareWithS1New
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      leaves d public1 proof hash obs g = .ok (.Ok p, scratch) := hprep
  obtain ⟨hcanonical, hpowers⟩ :=
    AspisR1S4PrepareInstalledMeaningV1.parent_success_installed_meaning
      sampling embed leaves d public1 proof hash obs g p scratch hbody
  exact ⟨hcanonical, hpowers, scratch_stage_map scratch⟩

#print axioms actual_prepared_gamma_meaning
end AspisR1S4Tx1ActualGammaBridgeV1
