import S4CandidatePrepareS1ParentV1
import S4InstalledEarlyPowersEquationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4InstalledPrepareRawEarlyPowersV1

private theorem bind_ok_inv {α β : Type} {m : Result α} {f : α → Result β} {v : β}
    (h : (do let x ← m; f x) = .ok v) : ∃ x, m = .ok x ∧ f x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- A successful execution of the installed source-shaped prepare slot exposes
    the actual generated early_powers result on the returned gamma. This is the
    same scratch array returned by that prepare execution. -/
theorem successful_prepare_exposes_generated_powers
    {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (ops : AspisR1S4CandidatePrepareS1ParentV1.Leaves H)
    (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (g : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (out : AspisR1CurrentCaller.verifier.Prepared)
    (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (h : AspisR1S4CandidatePrepareS1ParentV1.prepareSlot
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      ops d public1 proof hash obs g = .ok (.Ok out, scratch)) :
    ∃ raw : Array AspisR1LoopPowers.field.WideExact 29#usize,
      AspisR1LoopPowers.weights.early_powers 29#usize
        (AspisR1CurrentPreparedClaim.ClaimPowers.toPowers
          (AspisR1ClaimPreparedBridge.toClaimE
            (AspisR1S4PreparedNewS1AdapterV1.wToP out.gamma))) = .ok raw ∧
      AspisR1S4PreparedNewS1AdapterV1.wArrayFromP
        (AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.fromClaimE
          (AspisR1CurrentPreparedClaim.ClaimPowers.mapArray raw)) = scratch := by
  let B := AspisR1ClaimPreparedBridge.concreteBoundaries
    (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed)
  have hbody : AspisR1S4CandidatePrepareS1ParentV1.prepareWithS1New B
      ops d public1 proof hash obs g = .ok (.Ok out, scratch) := by
    simpa only [AspisR1S4CandidatePrepareS1ParentV1.prepareSlot] using h
  obtain ⟨gamma, powers, hout, hpowers, hscratch⟩ :=
    AspisR1S4CandidatePrepareS1ParentV1.prepareWithS1New_success_powers
      B ops d public1 proof hash obs g out scratch hbody
  have hbodyEarly :=
    AspisR1S4InstalledEarlyPowersEquationV1.installed_powers_eq_early_result
      sampling embed gamma
  have hpowersEarly :
      (do
        let raw ← AspisR1LoopPowers.weights.early_powers 29#usize
          (AspisR1CurrentPreparedClaim.ClaimPowers.toPowers
            (AspisR1ClaimPreparedBridge.toClaimE gamma))
        .ok (AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.fromClaimE
          (AspisR1CurrentPreparedClaim.ClaimPowers.mapArray raw))) = .ok powers := by
    rw [← hbodyEarly]
    exact hpowers
  obtain ⟨raw, hraw, hmap⟩ := bind_ok_inv hpowersEarly
  have hgammaMap : AspisR1S4PreparedNewS1AdapterV1.wToP out.gamma = gamma := by
    rw [hout]
    rfl
  have hinput := congrArg
    (fun x => AspisR1CurrentPreparedClaim.ClaimPowers.toPowers
      (AspisR1ClaimPreparedBridge.toClaimE x)) hgammaMap
  refine ⟨raw, ?_, ?_⟩
  · simpa only [hinput] using hraw
  · have hmapped :
        AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.fromClaimE
          (AspisR1CurrentPreparedClaim.ClaimPowers.mapArray raw) = powers := by
      cases hmap
      rfl
    rw [hmapped, hscratch]

#print axioms successful_prepare_exposes_generated_powers
end AspisR1S4InstalledPrepareRawEarlyPowersV1
