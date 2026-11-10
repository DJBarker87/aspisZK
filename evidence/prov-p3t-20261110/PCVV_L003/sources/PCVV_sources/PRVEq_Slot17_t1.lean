import Aeneas
import NNH_HostCtx
import NOC_Run5bHost
import AspisR1TerminalDecoder.Funs
import PRVEq_TD_HP_P3f
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1
set_option autoImplicit false
noncomputable section
namespace PCVV_Slot17

/-- The frozen (fresh PCQF_E002, overflow ON) emission of `pool_v1_pair_forest_output_lane_v1`. -/
abbrev fresh := @AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1

/-- The only error the frozen emission can return is NonCanonicalDigest (frozen source lines 184-191). -/
theorem fresh_err (d : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize)
    (e : AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
    (h : fresh d = ok (core.result.Result.Err e)) :
    e = AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.NonCanonicalDigest := by
  unfold fresh AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 at h
  cases hb : AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.digest_is_canonical d with
  | ok b =>
    rw [hb] at h
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_tc_ok] at h
      exact (core.result.Result.Err.inj (Result.ok.inj h)).symm
    · simp only [↓reduceIte, bind_tc_ok] at h
      cases hc : AspisR1TerminalDecoder.PRVFresh_TDf.pool_v1.pair_forest_accounts.first_canonical_byte d with
      | ok i => rw [hc] at h; simp only [bind_tc_ok] at h; cases h
      | fail e' => rw [hc] at h; cases h
      | div => rw [hc] at h; cases h
  | fail e' => rw [hb] at h; cases h
  | div => rw [hb] at h; cases h

/-- Slot op17 at the corrected seed, generic in the context: the deployed wrapper is the frozen emission followed by the
carrier conversion of its only error. The gate definition is equated to the frozen emission by PRVP3f.output_lane_eq. -/
theorem slot17 {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) (d : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize) :
    (AspisR1.NOC_HostCtx.sdk c).op17 d =
      (do let r ← fresh d
          match r with
          | core.result.Result.Err _ =>
            ok (core.result.Result.Err AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.NonCanonicalDigest)
          | core.result.Result.Ok lane => ok (core.result.Result.Ok lane)) := by
  show (do let result ← AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d
           match result with
           | core.result.Result.Err _ =>
             ok (core.result.Result.Err AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.NonCanonicalDigest)
           | core.result.Result.Ok lane => ok (core.result.Result.Ok lane)) = _
  rw [← PRVP3f.output_lane_eq]

#print axioms fresh_err
#print axioms slot17
end PCVV_Slot17
