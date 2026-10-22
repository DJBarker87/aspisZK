import S4CandidatePrepareS1ParentV1
import CurrentPreparedInstalledMeaning
import CurrentPreparedCandidateSamplers
import CurrentPreparedConcreteRun
import S4PreparedNewS1AdapterV1
import CallerStage2Carrier
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4PrepareInstalledMeaningV1
open AspisR1CurrentCaller
open AspisR1S4PreparedNewS1AdapterV1
open AspisR1ClaimPreparedBridge

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) : ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem body_success_model {H : Type}
    (B : AspisR1PublicPreparation.PreparedScratchModel.Boundaries)
    (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (v : AspisR1CurrentCaller.verifier.View) (hash : H)
    (out : AspisR1CurrentCaller.verifier.Prepared)
    (scratchIn scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (h : prepareByS1Body B d sem v hash scratchIn = .ok (.Ok out, scratch)) :
    ∃ (p : AspisR1PublicPreparation.verifier.Prepared)
      (scratchP : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
      AspisR1PublicPreparation.PreparedScratchModel.prepare B (currentDigestToP d)
        (verifiedToP sem) (viewToP v) hash (wArrayToP scratchIn) = .ok (.Ok p, scratchP) ∧
      preparedFromP p = out ∧ wArrayFromP scratchP = scratch := by
  unfold prepareByS1Body at h
  obtain ⟨pair, hmodel, hmap⟩ := bind_success _ _ _ h
  rcases pair with ⟨inner, scratchP⟩
  cases inner with
  | Err e => cases (Result.ok.inj hmap)
  | Ok p =>
      have heq : (mappedPreparedInner (.Ok p), wArrayFromP scratchP) = (.Ok out, scratch) :=
        Result.ok.inj hmap
      exact ⟨p, scratchP, by simpa using hmodel,
        by simpa [mappedPreparedInner] using congrArg Prod.fst heq,
        congrArg Prod.snd heq⟩

private theorem wide_roundtrip (x : AspisR1PublicPreparation.aspis_core.field.WideExact) :
    wToP (wFromP x) = x := by
  cases x with
  | mk q0 q1 => cases q0 with | mk a b => cases a; cases b; cases q1 with | mk c d => cases c; cases d; rfl

private theorem wide_array_roundtrip {n : Std.Usize}
    (x : Array AspisR1PublicPreparation.aspis_core.field.WideExact n) :
    wArrayToP (wArrayFromP x) = x := by
  apply Subtype.ext
  change (x.val.map wFromP).map wToP = x.val
  rw [List.map_map]
  have hid : (fun a => wToP (wFromP a)) = id := by funext a; exact wide_roundtrip a
  change List.map (fun a => wToP (wFromP a)) x.val = x.val
  rw [hid, List.map_id_fun]
  rfl

/-- The source-shaped candidate parent, with the accepted S1 constructor body,
    supplies canonical returned gamma, successful ClaimPowers for that gamma,
    and the mapped same-run scratch. All non-Prepared.new leaf operations are
    still explicit in `ops`. -/
theorem parent_success_installed_meaning {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (ops : AspisR1S4CandidatePrepareS1ParentV1.Leaves H) (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (g : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (out : AspisR1CurrentCaller.verifier.Prepared)
    (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (h : AspisR1S4CandidatePrepareS1ParentV1.prepareWithS1New
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      ops d public1 proof hash obs g = .ok (.Ok out, scratch)) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical
      (AspisR1ClaimPreparedBridge.toClaimE (wToP out.gamma)) ∧
    AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
      (AspisR1ClaimPreparedBridge.toClaimE (wToP out.gamma)) =
      .ok (AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.toClaimE
        (wArrayToP scratch)) := by
  obtain ⟨sem, v, hchild⟩ := AspisR1S4CandidatePrepareS1ParentV1.prepareWithS1New_success_child
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      ops d public1 proof hash obs g out scratch h
  obtain ⟨p, scratchP, hmodel, hprepared, hscratch⟩ := body_success_model
    (AspisR1ClaimPreparedBridge.concreteBoundaries
      (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
    d sem v hash out g scratch hchild
  let S := AspisR1PublicPreparation.PreparedFromQmSourceBridge.withSourceFromQm
    (AspisR1ClaimPreparedBridge.CurrentQueryRho.withConcreteQueries sampling embed)
  rw [AspisR1ClaimPreparedBridge.InstalledMeaning.installed_as_candidate_samplers] at hmodel
  have hcan := AspisR1ClaimPreparedBridge.prepared_candidate_samplers_canonical
    S (currentDigestToP d) (verifiedToP sem) (viewToP v) hash p scratchP (wArrayToP g) hmodel
  have hrun := AspisR1ClaimPreparedBridge.prepared_success_concrete_claim
    (withCandidateSamplers S) (currentDigestToP d) (verifiedToP sem) (viewToP v) hash p scratchP
    (wArrayToP g) hmodel
  have hgamma : wToP out.gamma = p.gamma := by
    have hg : out.gamma = wFromP p.gamma := by
      have he := congrArg AspisR1CurrentCaller.verifier.Prepared.gamma hprepared
      simpa [preparedFromP] using he.symm
    rw [hg]
    exact wide_roundtrip p.gamma
  have hscratch' : wArrayToP scratch = scratchP := by
    have he := congrArg wArrayToP hscratch
    simpa only [wide_array_roundtrip] using he.symm
  constructor
  · rw [hgamma]
    exact hcan.1
  · rw [hgamma, hscratch']
    exact hrun.1

#print axioms parent_success_installed_meaning
end AspisR1S4PrepareInstalledMeaningV1
