import NDO_JFs_Cell00
import NDO_JFs_Cell01
import NDO_JFs_Cell02
import NDO_JFs_Cell03
import NDO_JFs_LateDecode
import NDO_JFs_PaymentValue
import NDO_JFt_Digest00
set_option autoImplicit false
namespace AspisR1.JFs_PublicValue
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

def common : PoolV1PairForestTerminalCommonV1 :=
  {master_account:=JFs_Cell00.value,checkpoint_account:=JFs_Cell01.value,
   selected_lane_account:=JFs_Cell02.value,output_lane:=3#u8,
   checkpoint_sequence:=core.num.U64.from_le_bytes JFs_Cell03.value,
   historical_global_anchor:=JFt_Digest00.value,lane_transition:=JFs_LateChildren.value}

def value : PoolV1PairForestTerminalStatementV1 := .PrivateTransfer common JFs_PaymentValue.value

theorem sequence : core.num.U64.from_le_bytes JFs_Cell03.value=42#u64 := by rfl

theorem payment_pool : JFs_PaymentValue.common.pool=common.master_account := by rfl

theorem snapshot_pool : JFt_SnapshotValue.value.pool=common.master_account := by rfl

theorem payment_domain : JFs_PaymentValue.common.deployment_domain=
    JFt_SnapshotValue.value.deployment_domain := by rfl

theorem anchor : JFt_Digest43.value=common.historical_global_anchor := by rfl

theorem master_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    common.master_account (Array.repeat 32#usize 0#u8)=ok false := by rfl

theorem checkpoint_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    common.checkpoint_account (Array.repeat 32#usize 0#u8)=ok false := by rfl

theorem lane_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    common.selected_lane_account (Array.repeat 32#usize 0#u8)=ok false := by rfl

#print axioms sequence
#print axioms payment_pool
#print axioms snapshot_pool
#print axioms payment_domain
#print axioms anchor
#print axioms master_nonzero
#print axioms checkpoint_nonzero
#print axioms lane_nonzero
end AspisR1.JFs_PublicValue
