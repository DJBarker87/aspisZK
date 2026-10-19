import Stage2AuthExplicitBoundaries
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2AdoptedCaller.Stage2AuthSuccess
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem authenticated_success {H : Type} (b : Stage2AuthBoundaries H)
    (inst : aspis_core.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8)
    (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (h : verifier.candidate.tx2_authenticated b inst public_bytes proof checkpoint hash obs =
      ok (.Ok ())) :
    ∃ variant, b.parse_shape proof = ok (.Ok variant) ∧
      verifier.mark obs verifier.Phase.Parsed = ok () ∧
      b.tx2_common inst public_bytes proof checkpoint hash obs = ok (.Ok ()) := by
  unfold verifier.candidate.tx2_authenticated at h
  obtain ⟨r, hr, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok variant =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    obtain ⟨unit, hm, ht⟩ := bind_success _ _ _ h
    cases unit
    exact ⟨variant, hr, hm, ht⟩
#print axioms authenticated_success
end AspisR1Stage2AdoptedCaller.Stage2AuthSuccess
