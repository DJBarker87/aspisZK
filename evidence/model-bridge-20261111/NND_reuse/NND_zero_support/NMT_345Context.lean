import NMT_stage1_owned.Funs
import RSL_TX1_345
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
abbrev PE := NMT_stage1_owned.solana_program_error.ProgramError
abbrev Account := NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount
abbrev Key := NMT_stage1_owned.solana_pubkey.Pubkey
abbrev Ret := core.result.Result (alloc.vec.Vec U8) PE
/-- Fresh E003 opaque interfaces. SUPPORT ONLY, never a row-root hypothesis.
Each field must be concretely installed before a candidate exists. -/
structure Calls where
 c0 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
    T U),
  (Slice T) → (Array U N) → Result Bool
 c1 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
    T U),
  (Slice T) → (Array U N) → Result Bool
 c2 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
    core.ops.function.FnOnce O E F),
  (core.result.Result T E) → O → Result (core.result.Result T F)
 c3 : aspis_r1_cost_probe.transport.Variant → Result Std.U8
 c4 : Result Std.Usize
 c5 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
      → Result aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
 c6 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
      → Result
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
 c7 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
      → Result (core.result.Result Unit
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
 c8 : Result Std.Usize
 c9 : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 →
      Result (core.result.Result (Array Std.U8 688#usize)
      aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
 c10 : solana_program_error.ProgramError → Result
      solana_program_error.ProgramError
 c11 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
      Std.U8) → (Slice Std.U8) → Std.Usize → Result (core.result.Result
      (alloc.vec.Vec Std.U8) solana_program_error.ProgramError)
 c12 : (Slice Std.U8) → Result (core.result.Result
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
      solana_program_error.ProgramError)
 c13 : r1_pool_adapter.owned.OwnedAccount → Result (core.result.Result Unit
      solana_program_error.ProgramError)
 c14 : r1_pool_adapter.owned.OwnedAccount → solana_pubkey.Pubkey → Bool →
      Result (core.result.Result Unit solana_program_error.ProgramError)
 c15 : ∀ {N : Std.Usize},
  (Array r1_pool_adapter.owned.OwnedAccount N) → Result (core.result.Result
      Unit solana_program_error.ProgramError)
 c16 : (Slice Std.U8) → Result (core.result.Result Unit
      solana_program_error.ProgramError)
/-- A single parent state retains original arguments, ambient world and
ordered effect prefix. Phase extensions add locals without projecting world. -/
structure Parent (W : Type) where
 program : Key
 accounts : Slice Account
 data : Slice U8
 world : W
 events : List RSL.Event

def emitted {W : Type} (c : Calls) (s : Parent W) : Result Ret :=
 NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned c.c0 c.c1 c.c2 c.c3 c.c4 c.c5 c.c6 c.c7 c.c8 c.c9 c.c10 c.c11 c.c12 c.c13 c.c14 c.c15 c.c16 s.program s.accounts s.data

end NMT_345
