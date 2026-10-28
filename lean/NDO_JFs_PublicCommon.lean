import NDO_JFs_PublicReads
import NDO_JFs_PublicSize
import NDO_JFs_PublicHeader
set_option autoImplicit false
namespace AspisR1.JFs_PublicCommon
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

theorem late : decode_lane_transition_boxed_v1 JFu_PublicRange.late=
    ok (.Ok JFs_LateChildren.value) := by
  unfold decode_lane_transition_boxed_v1
  rw [JFs_LateDecode.source]
  rfl

theorem source : decode_terminal_common_boxed_v1 JFx_NativeBytes.publicInput=
    ok (.Ok JFs_PublicValue.common) := by
  have lateCall:=late
  unfold JFu_PublicRange.late at lateCall
  have b7:=JFs_PublicHeader.index 7#usize (by decide) 3#u8 (by rfl)
  unfold decode_terminal_common_boxed_v1
  simp only [HISTORICAL_ANCHOR_OFFSET,LATE_STATEMENT_OFFSET,MASTER_OFFSET,
    CHECKPOINT_ACCOUNT_OFFSET,SELECTED_LANE_ACCOUNT_OFFSET,CHECKPOINT_SEQUENCE_OFFSET,
    JFs_PublicSize.payment_offset]
  simp only [
    JFu_PublicRange.read 112#usize 144#usize (by decide) (by decide),
    JFu_PublicRange.read 144#usize 1664#usize (by decide) (by decide),
    JFu_PublicRange.read 8#usize 40#usize (by decide) (by decide),
    JFu_PublicRange.read 40#usize 72#usize (by decide) (by decide),
    JFu_PublicRange.read 72#usize 104#usize (by decide) (by decide),
    JFu_PublicRange.read 104#usize 112#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,
    show (72#usize).val=72 from rfl,
    show (104#usize).val=104 from rfl,
    show (112#usize).val=112 from rfl,
    show (144#usize).val=144 from rfl,
    show (1664#usize).val=1664 from rfl,
    Nat.reduceSub,JFs_PublicReads.root_shared,JFs_PublicReads.root_decode,
    JFs_PublicReads.cast0,JFs_PublicReads.cast1,JFs_PublicReads.cast2,JFs_PublicReads.cast3,
    lateCall,b7,bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,lift]
  rfl

#print axioms late
#print axioms source
end AspisR1.JFs_PublicCommon
