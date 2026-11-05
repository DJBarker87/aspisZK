import NHC_HintsTotal
import NHC_NGG_RequestLength
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NHC_HintDecoderDomain
/-- Derive the request window from the actual emitted splitter result and the
S packet's accepted decoder result. Neither length is an input premise. -/
theorem accepted_length (whole body : Slice U8)
    (hints : NHC_Hints.pair_forest.PoolV1PairForestTerminalBumpHintsV1)
    (request : AspisR1.NFY_JHd_RequestNative.Request)
    (stripped : NHC_Hints.pair_forest.split_pair_forest_terminal_bump_hints_v1 whole =
      ok (.Ok (body,hints)))
    (decoded : AspisR1.NFY_JHd_RequestNative.decode body = ok (.Ok request)) :
    whole.val.length = 324 ∧ body.val.length = 320 := by
  have lower : 4 ≤ whole.val.length := by
    by_contra bad
    have short := NHC_HintsTotal.short whole (by omega)
    rw [stripped] at short
    cases short
  obtain ⟨body',hints',run,window,_⟩ := NHC_HintsTotal.split whole lower
  have same : (body',hints') = (body,hints) :=
    core.result.Result.Ok.inj (Result.ok.inj (run.symm.trans stripped))
  have hb : body' = body := congrArg Prod.fst same
  rw [hb] at window
  exact ⟨NHC_NGG_RequestLength.payload whole body request lower window decoded,
    NHC_NGG_RequestLength.decoder body request decoded⟩
#print axioms accepted_length
end NHC_HintDecoderDomain
