import AspisR1ViewParseProbe.ViewEcheckLoopTransfer

set_option autoImplicit false

namespace AspisR1ViewParseProbe.ViewEcheckRound1Transfer
open Aeneas Aeneas.Std Result
open AspisR1ViewParseProbe.ViewEcheckLoopSuccess
open AspisR1ViewParseProbe.ViewEcheckLoopTransfer

theorem echeck_round1_success_transfer (bytes : Slice U8)
    (h : AspisR1ViewParseProbe.verifier.echeck bytes false =
      ok (core.result.Result.Ok ())) :
    AspisR1EcheckCut.verifier.echeck_round1 bytes =
      ok (core.result.Result.Ok ()) := by
  unfold AspisR1ViewParseProbe.verifier.echeck at h
  cases hc : core.slice.Slice.chunks_exact bytes 32#usize with
  | fail e =>
      have hf : False := by simp [hc, bind_tc_fail] at h
      exact hf.elim
  | div =>
      have hf : False := by simp [hc, bind_tc_div] at h
      exact hf.elim
  | ok iter =>
      simp only [hc, bind_tc_ok] at h
      have hparsed := loop_success_echeckcut iter h
      have hloop := echeckcut_loop_success_from_parses iter hparsed
      unfold AspisR1EcheckCut.verifier.echeck_round1
        AspisR1EcheckCut.verifier.echeck
      simp only [hc, bind_tc_ok]
      exact hloop

#print axioms echeck_round1_success_transfer

end AspisR1ViewParseProbe.ViewEcheckRound1Transfer
