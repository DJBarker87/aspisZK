import AspisR1TerminalDecoder.Funs
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
namespace R1Z.PV_RunJoin_DecoderReturn29
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder.pool_v1.pair_tree_profile

theorem branch_continue {α ε : Type} (r : core.result.Result α ε) (a : α)
    (h : core.result.Result.Insts.CoreOpsTry.branch r = ok (.Continue a)) :
    r = .Ok a := by
  cases r with
  | Ok b => cases h; rfl
  | Err e => cases h
#print axioms branch_continue

/-- Successful decoding of the actual pinned extraction includes successful
validation of exactly the returned snapshot, preserving both Result layers. -/
theorem validated (bytes : Slice U8) (snapshot : PoolV1PairLiveSnapshotV1)
    (h : decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Ok snapshot)) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ()) := by
  unfold decode_pool_v1_pair_live_snapshot_v1 at h
  dsimp only at h
  repeat' first
    | (have hr := branch_continue _ _ hvalue; clear hvalue; cases hr)
    | (pv_peel h with value hvalue; dsimp only at h)
    | (split at h <;> dsimp only at h)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true, ↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; assumption)
#print axioms validated
end R1Z.PV_RunJoin_DecoderReturn29
