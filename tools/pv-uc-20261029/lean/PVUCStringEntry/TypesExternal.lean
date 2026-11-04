import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_UC_StringEntry

class ExternalTypes where
  op0 : Type
  op1 : Type
  op2 : Type
  op3 : Type
  op4 : Type
  op5 : Type
  op6 : Type
  op7 : Type
  op8 : Type
  op9 : Type
  op10 : Type
  op11 : Type
  op12 : Type
  op13 : Type
  op14 : Type
  op15 : Type
  op16 : Type
  op17
  : Type
  op18
  : Type
  op19 : Type
  op20 (K : Type) (V : Type) : Type
  op21 : Type
  op22 : Type
  op23 : Type

abbrev core.io.error.ErrorKind [ext : ExternalTypes] := @ExternalTypes.op0 ext
abbrev core.num.error.ParseIntError [ext : ExternalTypes] := @ExternalTypes.op1 ext
abbrev core.time.Duration [ext : ExternalTypes] := @ExternalTypes.op2 ext
abbrev std.ffi.os_str.OsStr [ext : ExternalTypes] := @ExternalTypes.op3 ext
abbrev std.fs.File [ext : ExternalTypes] := @ExternalTypes.op4 ext
abbrev std.path.Path [ext : ExternalTypes] := @ExternalTypes.op5 ext
abbrev std.io.error.Error [ext : ExternalTypes] := @ExternalTypes.op6 ext
abbrev std.io.stdio.Stdin [ext : ExternalTypes] := @ExternalTypes.op7 ext
abbrev std.io.stdio.Stderr [ext : ExternalTypes] := @ExternalTypes.op8 ext
abbrev std.path.PathBuf [ext : ExternalTypes] := @ExternalTypes.op9 ext
abbrev std.time.Instant [ext : ExternalTypes] := @ExternalTypes.op10 ext
abbrev alloc.string.FromUtf8Error [ext : ExternalTypes] := @ExternalTypes.op11 ext
abbrev solana_program_error.ProgramError [ext : ExternalTypes] := @ExternalTypes.op12 ext
abbrev aspis_statement.state_only_trace.StateOnlyTraceFoundation [ext : ExternalTypes] := @ExternalTypes.op13 ext
abbrev aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1 [ext : ExternalTypes] := @ExternalTypes.op14 ext
abbrev aspis_r1_cost_probe.prover.MaskedFixtureAudit [ext : ExternalTypes] := @ExternalTypes.op15 ext
abbrev aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError [ext : ExternalTypes] := @ExternalTypes.op16 ext
abbrev aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError [ext : ExternalTypes] := @ExternalTypes.op17 ext
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 [ext : ExternalTypes] := @ExternalTypes.op18 ext
abbrev serde_json.error.Error [ext : ExternalTypes] := @ExternalTypes.op19 ext
abbrev serde_json.map.Map [ext : ExternalTypes] := @ExternalTypes.op20 ext
abbrev serde_json.value.Value [ext : ExternalTypes] := @ExternalTypes.op21 ext
abbrev serde_json.number.Number [ext : ExternalTypes] := @ExternalTypes.op22 ext
abbrev solana_pubkey.ParsePubkeyError [ext : ExternalTypes] := @ExternalTypes.op23 ext

end PV_UC_StringEntry
