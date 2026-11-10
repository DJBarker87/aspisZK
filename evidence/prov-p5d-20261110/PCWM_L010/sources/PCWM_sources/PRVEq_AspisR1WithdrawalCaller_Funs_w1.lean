-- PCWM_ w1: fresh frozen-4bb3b3f (overflow checks ON) definitions of the five WithdrawalCaller.Funs items that are not loops, against the gate constants.
-- fresh sources: spend.VALUE_LIMIT <- PCQF_E003; POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_TREE_DEPTH <- PCQF_E010; POOL_V1_LEAF_CAPACITY <- PCQF_E004; M31.to_le_bytes <- PCWM_E001. Text is verbatim.
import Aeneas
import AspisR1WithdrawalCaller.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace AspisR1WithdrawalCaller
namespace PRVFresh_AspisR1WithdrawalCaller_Funs_w1
/-- fresh type aspis_core::field::M31 (frozen Types text: `def field.M31 := Std.U32`) -/
@[reducible] def field.M31 := Std.U32
/-- [aspis_statement::spend::VALUE_LIMIT]
    Source: 'crates/aspis-statement/src/spend.rs', lines 9:0-9:37
    Visibility: public -/
@[global_simps, irreducible]
def spend.VALUE_LIMIT : Result Std.U32 := 1#u32 <<< 30#i32

/-- [aspis_statement::pool_v1::format::POOL_V1_DIGEST_ENCODING_VERSION]
    Source: 'crates/aspis-statement/src/pool_v1/format.rs', lines 27:0-27:50
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION : Std.U8 := 1#u8

/-- [aspis_statement::pool_v1::format::POOL_V1_TREE_DEPTH]
    Source: 'crates/aspis-statement/src/pool_v1/format.rs', lines 28:0-28:41
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.format.POOL_V1_TREE_DEPTH : Std.Usize := 20#usize

/-- [aspis_statement::pool_v1::incremental_merkle::POOL_V1_LEAF_CAPACITY]
    Source: 'crates/aspis-statement/src/pool_v1/incremental_merkle.rs', lines 26:0-26:66
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY : Result Std.U64 :=
  1#u64 <<< pool_v1.format.POOL_V1_TREE_DEPTH

/-- [aspis_core::field::{aspis_core::field::M31}::to_le_bytes]:
    Source: 'crates/aspis-core/src/field.rs', lines 248:4-250:5
    Visibility: public -/
def field.M31.to_le_bytes
  (self : field.M31) : Result (Array Std.U8 4#usize) := do
  ok (core.num.U32.to_le_bytes self)


end PRVFresh_AspisR1WithdrawalCaller_Funs_w1
end AspisR1WithdrawalCaller

namespace PRVEq.AspisR1WithdrawalCaller.Funs_w1
open AspisR1WithdrawalCaller

theorem pool_v1.POOL_V1_TREE_DEPTH : AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.format.POOL_V1_TREE_DEPTH = AspisR1WithdrawalCaller.pool_v1.POOL_V1_TREE_DEPTH := by
  unfold AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.format.POOL_V1_TREE_DEPTH AspisR1WithdrawalCaller.pool_v1.POOL_V1_TREE_DEPTH; rfl
#print axioms pool_v1.POOL_V1_TREE_DEPTH

theorem pool_v1.POOL_V1_DIGEST_ENCODING_VERSION : AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION = AspisR1WithdrawalCaller.pool_v1.POOL_V1_DIGEST_ENCODING_VERSION := by
  unfold AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION AspisR1WithdrawalCaller.pool_v1.POOL_V1_DIGEST_ENCODING_VERSION; rfl
#print axioms pool_v1.POOL_V1_DIGEST_ENCODING_VERSION

theorem VALUE_LIMIT : AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.spend.VALUE_LIMIT = AspisR1WithdrawalCaller.VALUE_LIMIT := by
  unfold AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.spend.VALUE_LIMIT AspisR1WithdrawalCaller.VALUE_LIMIT; rfl
#print axioms VALUE_LIMIT

/-- the fresh capacity is `1 <<< fresh TREE_DEPTH`, the gate's is `1 <<< gate TREE_DEPTH`; equal by the depth equality -/
theorem pool_v1.POOL_V1_LEAF_CAPACITY : AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY = AspisR1WithdrawalCaller.pool_v1.POOL_V1_LEAF_CAPACITY := by
  unfold AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY AspisR1WithdrawalCaller.pool_v1.POOL_V1_LEAF_CAPACITY
  rw [pool_v1.POOL_V1_TREE_DEPTH]
#print axioms pool_v1.POOL_V1_LEAF_CAPACITY

theorem aspis_core.field.M31.to_le_bytes : @AspisR1WithdrawalCaller.PRVFresh_AspisR1WithdrawalCaller_Funs_w1.field.M31.to_le_bytes = @AspisR1WithdrawalCaller.aspis_core.field.M31.to_le_bytes := by
  rfl
#print axioms aspis_core.field.M31.to_le_bytes

end PRVEq.AspisR1WithdrawalCaller.Funs_w1
