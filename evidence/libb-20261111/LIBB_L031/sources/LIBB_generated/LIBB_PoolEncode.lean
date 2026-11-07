import LIBB_ModelGraph
import LIBB_PoolCarriers
import LIBB_V1DecoderValues
import NFY_Part053
set_option autoImplicit false
noncomputable section
namespace LIBB_PoolEncode
open Aeneas Aeneas.Std
abbrev terminal := AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1
/-- The CLOSED encoder returns its 1880-byte array by value. No allocation
site is inserted at this call. -/
def code (s : LIBB_PoolCarriers.Statement) := AspisS6OuterNativeInstalled.encode (terminal s)
def option : core.result.Result (Array U8 1880#usize) AspisS6OuterNativeInstalled.Error → Option RSL.Bytes := LIBB_V1DecoderValues.asOption (fun a : Array U8 1880#usize => LIB_Carriers.bytes a.to_slice)
def encodeStatement (s : LIBB_PoolCarriers.Statement) : RSL.Spec (Option RSL.Bytes) :=
 RSL.Spec.map option (NMS_R2N_Interpreted.liftResult (code s))
def evaluator (s : LIBB_PoolCarriers.Statement) : Option RSL.Bytes :=
 option (LIBB_ModelGraph.value (.Err .WrongLength) (code s))

/-- Supplying CLOSED165 root applied at the SAME fully converted statement. -/
theorem root (s : LIBB_PoolCarriers.Statement) :
 (NFY_NEQ_EncoderOracle.run
   AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
   NFY_NEM_PaymentReached.pay NFY_NEM_LateOracle.late
   AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical (terminal s)).1 =
 NFY_NBN_StatementEncoderSummary.observe (code s) :=
 congrArg Prod.fst (NFY_NEQ_EncoderOracle.result_state_effects (terminal s) ())

theorem returns (s : LIBB_PoolCarriers.Statement) (env : RSL.Env) :
 NND_Returned.Returns (encodeStatement s) env (evaluator s) :=
 NND_Returned.map _ option env _ (LIBB_ModelGraph.lift_returned (code s) _ env)

/-- Every successful encoding has the exact statement width, proved on the
array carrier without normalizing any concrete output bytes. -/
theorem width (s : LIBB_PoolCarriers.Statement)
 (raw : core.result.Result (Array U8 1880#usize) AspisS6OuterNativeInstalled.Error)
 (bytes : RSL.Bytes) (same : option raw = some bytes) : bytes.length = 1880 := by
 cases raw with
 | Err e => cases same
 | Ok a =>
   have hb : LIB_Carriers.bytes a.to_slice = bytes := Option.some.inj same
   rw [←hb, NMS_R2N_RSLScalars.bytes_length]
   exact a.property
#print axioms root
#print axioms returns
#print axioms width
end LIBB_PoolEncode
end
