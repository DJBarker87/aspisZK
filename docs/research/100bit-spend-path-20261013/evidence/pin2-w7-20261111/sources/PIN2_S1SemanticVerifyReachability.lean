import PIN2_NEWGATE_verifyprefix
/-! PIN2 W7 (2026-11-11): the frozen `AspisR1PublicPreparation.S1SemanticVerify.verify_success`
(RPz7_S1SemanticVerifyReachabilityV1), stated over W8's PIN2 emission
`PIN2_NEWGATE_verifyprefix` (namespace `AspisR1PublicPreparationPIN2`, twin types).
Statement text identical except the digest trait path (`aspis_core.digest.Digest32`,
the emission's name); the proof unfolds the PCWN_NewLib `branch`/`from_residual`
the emission uses in place of the Aeneas.Std ones.  New module: the frozen one stays. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparationPIN2.S1SemanticVerify
open AspisR1PublicPreparationPIN2
open VerifyPrefix

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem pair_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok p => cases p with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- No helper-success premise: actual successful verifier prefix supplies it. -/
theorem verify_success (F : Finish) {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (h : verify F D pub bytes hash obs = ok (.Ok out)) :
    ∃ pre initial after challenges,
      PrefixAdapter.parseAccepted bytes = ok (.Ok pre) ∧
      r1_semantic.public_transcript D pub hash pre.c1_root = ok (.Ok initial) ∧
      r1_wire.begin D pre initial = ok (.Ok challenges, after) ∧
      F D pub pre after challenges obs = ok (.Ok out) := by
  unfold verify at h
  obtain ⟨pr, hp, h⟩ := bind_success _ _ _ h
  cases pr with
  | Err e =>
    simp only [PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
      PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok] at h
    cases h
  | Ok pre =>
    simp only [PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, mark] at h
    obtain ⟨tr, ht, h⟩ := bind_success _ _ _ h
    cases tr with
    | Err e =>
      simp only [PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at h
      cases h
    | Ok initial =>
      simp only [PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      obtain ⟨cr, after, hb, h⟩ := pair_success _ _ _ h
      cases cr with
      | Err e =>
        simp only [PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
          PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok] at h
        cases h
      | Ok challenges =>
        simp only [PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, mark] at h
        exact ⟨pre, initial, after, challenges, hp, ht, hb, h⟩


#print axioms verify_success
end AspisR1PublicPreparationPIN2.S1SemanticVerify
