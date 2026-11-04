import NFR_RawInverseValidator
set_option autoImplicit false
noncomputable section
namespace NFR_RawInverseFrames
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open AspisR1.S2K NFO_ResultLayout

theorem branch_continue {T E : Type} (r : core.result.Result T E) (v : T) :
    core.result.Result.Insts.CoreOpsTry.branch r =
      ok (core.ops.control_flow.ControlFlow.Continue v) ↔ r = .Ok v := by
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch]
#print axioms branch_continue

@[simp] theorem kind_discriminant (k : pool_v1.historical_anchor.PoolV1TransitionKind) :
    kind k = (read_discriminant k : U8) := by
  cases k <;> rfl
#print axioms kind_discriminant

def Frame (bytes : Slice U8) (value : Output) : Prop :=
  bytes.val.length = 792 ∧
  bytes.val.take 4 = [65#u8,83#u8,82#u8,56#u8] ∧
  bytes.val[4]? = some (1#u8) ∧
  bytes.val[5]? = some (kind value.transition_kind) ∧
  bytes.val[6]? = some (1#u8) ∧
  bytes.val[7]? = some value.output_lane ∧
  value.master_account.val = List.slice 8 40 bytes.val ∧
  value.selected_lane_account.val = List.slice 40 72 bytes.val ∧
  (DigestBytes.bytes value.nullifier).val = List.slice 72 104 bytes.val ∧
  (AfterstateEncoding.bytes value.verified_afterstate).val = bytes.val.drop 104

theorem frames (bytes : Slice U8) :
    NFO_RawDecode.decode bytes ⦃ result => ∀ value, result = .Ok value → Frame bytes value ⦄ := by
  unfold NFO_RawDecode.decode core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  simp only [pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET,
    pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET,
    pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET,
    pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET]
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*
  all_goals try scalar_tac
  all_goals have hlen : bytes.val.length = 792 := by scalar_tac
  all_goals simp_all [branch_continue,Frame,
    pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC,
    pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    List.getElem?_eq_getElem,Array.make]
  all_goals repeat' constructor
  all_goals scalar_tac
#print axioms frames
end NFR_RawInverseFrames
