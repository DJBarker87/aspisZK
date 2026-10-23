import S2SdkReadyRawInputsV1

/-! Concrete installed child carriers at ONE caller cut. These theorems consume
an observation of that cut, not an independently existential successful run.
They do not produce the observation from native adapter acceptance. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2A.InstalledCuts
open AspisS2OwnedStage1 AspisS2OwnedStage1.SdkReference
open ReadyStatement

/-- Same complete returned statement, same input slice, and the validator that
was actually executed inside the installed decoder. No successful validator
observation needs to be independently supplied. -/
theorem decoded (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (originalPublic : Slice U8) (statement : Statement)
    (observed : SdkReference.decode_public_statement_box
      (Installation.install ops verifierOps) originalPublic = ok (.Ok statement)) :
    ∃ decoded : AspisR1TerminalDecoder.PublicBinding.Statement,
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual originalPublic = ok (.Ok decoded) ∧
      statement = CurrentCarrier.fromDecoderStatement decoded ∧
      originalPublic.val.length = 1880 ∧
      (Installation.install ops verifierOps).op5 statement = ok (.Ok ()) := by
  rw [Installation.boxed_eq] at observed
  have actual : SourceInstallation.actualDecoder originalPublic = ok (.Ok statement) :=
    SourceInstallation.boxed_success _ originalPublic statement observed
  obtain ⟨value, success, same⟩ := SourceInstallation.decoder_success originalPublic statement actual
  exact ⟨value, success, same,
    (AspisR1TerminalDecoder.DecoderSuccess.decode_success originalPublic value success).2.1,
    SourceInstallation.decoder_validated originalPublic statement actual⟩

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a) = ok out) : ∃ a, m = ok a ∧ f a = ok out := by
  cases m with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Invert the installed encoder on the candidate-afterstate of the very same
full statement. The successful output is the identical 688-byte Array carrier,
with no independently chosen common/public witness or encoder output. -/
theorem encoded (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (statement : Statement) (candidate : Array U8 688#usize)
    (observed : (Installation.install ops verifierOps).op8
      (commonOf statement).lane_transition.candidate_afterstate = ok (.Ok candidate)) :
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
      (CurrentCarrier.toDecoderAfterstate (commonOf statement).lane_transition.candidate_afterstate) =
        ok (.Ok candidate) := by
  change SourceInstallation.actualEncoder _ = ok (.Ok candidate) at observed
  unfold SourceInstallation.actualEncoder at observed
  obtain ⟨reply, returned, observed⟩ := bind_success _ _ _ observed
  cases reply with
  | Err e => cases observed
  | Ok value => cases observed; exact returned

#print axioms decoded
#print axioms bind_success
#print axioms encoded
end AspisR1.S2A.InstalledCuts
