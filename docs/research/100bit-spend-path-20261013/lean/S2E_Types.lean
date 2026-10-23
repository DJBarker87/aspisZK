import S2SdkOwnedTypesV1
open Aeneas Aeneas.Std Result ControlFlow Error AspisS2OwnedStage1
namespace S2E_Reference
/-- [core::ops::range::RangeFull]
    Source: '/rustc/library/core/src/ops/range.rs', lines 44:0-44:20
    Name pattern: [core::ops::range::RangeFull]
    Visibility: public -/
@[reducible, rust_type "core::ops::range::RangeFull"]
def core.ops.range.RangeFull := Unit

abbrev S2E_Reference.OwnedLamportsCell := AspisS2OwnedStage1.SdkReference.OwnedLamportsCell

abbrev S2E_Reference.OwnedDataCell := AspisS2OwnedStage1.SdkReference.OwnedDataCell

abbrev S2E_Reference.OwnedAccount := AspisS2OwnedStage1.SdkReference.OwnedAccount

abbrev S2E_Reference.OwnedSdk := AspisS2OwnedStage1.SdkReference.OwnedSdk

/-- [s2e_reference::S2E_Reference::Validated]
    Source: 'src/S2E_Reference.rs', lines 31:0-31:79
    Visibility: public -/
structure S2E_Reference.Validated where
  statement :
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
  proof_length : Std.Usize

/-- Trait declaration: [s2e_reference::S2E_Reference::Children]
    Source: 'src/S2E_Reference.rs', lines 14:0-30:1
    Visibility: public -/
structure S2E_Reference.Children (Self : Type) (Self_State : Type) where
  decode : Self_State → (Slice Std.U8) → Result ((core.result.Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    solana_program_error.ProgramError) × Self_State)
  validate : Self_State →
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result ((core.result.Result Unit solana_program_error.ProgramError) ×
    Self_State)
  candidate : Self_State →
    aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 →
    Result ((core.result.Result (Array Std.U8 688#usize)
    solana_program_error.ProgramError) × Self_State)
  first : Self_State →
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → (Slice Std.U8) → (Slice Std.U8) → Std.Usize → Result
    ((core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError) × Self_State)
  copy : Self_State → S2E_Reference.OwnedSdk → Std.Usize → (Slice Std.U8)
    → Result (Self_State × S2E_Reference.OwnedSdk)
  drop_checkpoint : Self_State → (alloc.vec.Vec Std.U8) → Result Self_State
  drop_statement : Self_State →
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result Self_State
  validate_asq8 : Self_State → (Array Std.U8 32#usize) →
    S2E_Reference.OwnedSdk → (Slice Std.U8) → Result ((core.result.Result
    S2E_Reference.Validated solana_program_error.ProgramError) × Self_State)
  «public» : Self_State →
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result ((core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError) × Self_State)
  second : Self_State → (Slice Std.U8) → (Slice Std.U8) → (Slice Std.U8)
    → Result ((core.result.Result Unit solana_program_error.ProgramError) ×
    Self_State)
  emit : Self_State →
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result ((core.result.Result Unit solana_program_error.ProgramError) ×
    Self_State)
  clear_return_data : Self_State → Result Self_State

abbrev S2E_Reference.LiveGuards := AspisS2OwnedStage1.SdkReference.LiveGuards

/-- [s2e_reference::S2E_Reference::statement_continuation::closure#1]
    Source: 'src/S2E_Reference.rs', lines 140:14-140:49 -/
@[reducible]
def S2E_Reference.statement_continuation.closure_1 (C : Type) (Clause0_State :
  Type) :=
Unit

/-- [s2e_reference::S2E_Reference::statement_continuation::closure]
    Source: 'src/S2E_Reference.rs', lines 138:38-138:73 -/
@[reducible]
def S2E_Reference.statement_continuation.closure (C : Type) (Clause0_State :
  Type) :=
Unit

/-- [s2e_reference::S2E_Reference::stage2_tail::closure]
    Source: 'src/S2E_Reference.rs', lines 180:58-180:97 -/
@[reducible]
def S2E_Reference.stage2_tail.closure (C : Type) (Clause0_State : Type) := Unit
end S2E_Reference

#print axioms S2E_Reference.S2E_Reference.OwnedSdk
