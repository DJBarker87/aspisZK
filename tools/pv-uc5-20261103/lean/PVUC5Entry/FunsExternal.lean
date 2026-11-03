import Aeneas
import PVUC5Entry.Types
import PVUC5Entry.FloatCarrier
import PVUC5Entry.NativeConstants
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_UC5_Entry

class ExternalFuns [ExternalTypes] where
  op0
  {T : Type} {U : Type} (AsRefInst : core.convert.AsRef T U) : T → Result U
  op1
  :
  Std.U64 → Result (core.result.Result Std.U32
    core.num.error.TryFromIntError)
  op2
  :
  Std.U64 → Result (core.result.Result Std.I32
    core.num.error.TryFromIntError)
  op3
  :
  Str → Std.U32 → Result (core.result.Result Std.U8
    core.num.error.ParseIntError)
  op4 : Std.Usize → Std.Usize → Result Std.Usize
  op5
  {Idx : Type} {U : Type} (cmpPartialOrdInst : core.cmp.PartialOrd Idx Idx)
  (cmpPartialOrdInst1 : core.cmp.PartialOrd Idx U) (cmpPartialOrdInst2 :
  core.cmp.PartialOrd U Idx) :
  (core.ops.range.RangeInclusive Idx) → U → Result Bool
  op6
  {T : Type} {E : Type} {F : Type} (opsfunctionFnOnceFTupleEInst :
  core.ops.function.FnOnce F Unit E) :
  (Option T) → F → Result (core.result.Result T E)
  op7
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
  (Option T) → (Option T) → Result Bool
  op8
  {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) :
  (core.result.Result T E) → O → Result (core.result.Result T F)
  op9 : Str → Result Std.Usize
  op10 : Str → Result Bool
  op11 : Str → Str → Result Bool
  op12
  {I : Type} {Clause0_Output : Type}
  (sliceindexSliceIndexIStrClause0_OutputInst : core.slice.index.SliceIndex I
  Str Clause0_Output) :
  Str → I → Result Clause0_Output
  op13
  : (core.ops.range.Range Std.Usize) → Str → Result (Str × (Str → Str))
  op14
  : (core.ops.range.Range Std.Usize) → Str → Result Str
  op15
  :
  (core.ops.range.Range Std.Usize) → (MutRawPtr Str) → Result (MutRawPtr
    Str)
  op16
  :
  (core.ops.range.Range Std.Usize) → (ConstRawPtr Str) → Result
    (ConstRawPtr Str)
  op17
  :
  (core.ops.range.Range Std.Usize) → Str → Result ((Option Str) × (Option
    Str → Str))
  op18
  : (core.ops.range.Range Std.Usize) → Str → Result (Option Str)
  op19 : core.time.Duration → Result F64
  op20
  : String → Result std.ffi.os_str.OsStr
  op21
  {P : Type} {C : Type} (coreconvertAsRefPPathInst : core.convert.AsRef P
  std.path.Path) (coreconvertAsRefCSliceU8Inst : core.convert.AsRef C (Slice
  Std.U8)) :
  P → C → Result (core.result.Result Unit std.io.error.Error)
  op22 : Result std.io.stdio.Stdin
  op23
  :
  std.io.stdio.Stdin → String → Result ((core.result.Result Std.Usize
    std.io.error.Error) × std.io.stdio.Stdin × String)
  op24 : Result std.io.stdio.Stderr
  op25
  :
  std.io.stdio.Stderr → (Slice Std.U8) → Result ((core.result.Result Unit
    std.io.error.Error) × std.io.stdio.Stderr)
  op26
  {S : Type} (coreconvertAsRefSOsStrInst : core.convert.AsRef S
  std.ffi.os_str.OsStr) :
  S → Result std.path.Path
  op27
  : std.path.PathBuf → Result std.path.Path
  op28 : Std.I32 → Result Never
  op29 : Result std.time.Instant
  op30 : std.time.Instant → Result core.time.Duration
  op31 : Str → Result String
  op32 : Result String
  op33 : String → Result Str
  op34
  : String → Result Str
  op35
  {T : Type} (A : Type) : (alloc.vec.Vec T) → Result (Slice T)
  op36
  : aspis_core.field.M31 → aspis_core.field.M31 → Result Bool
  op37
  : Result (Array (Array aspis_core.field.M31 8#usize) 21#usize)
  op38
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Std.U64 → Result
    (solana_pubkey.Pubkey × Std.U8)
  op39
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → (Array Std.U8 32#usize) →
    Result (core.result.Result (solana_pubkey.Pubkey × (Array Std.U8
    32#usize)) solana_program_error.ProgramError)
  op40
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → solana_pubkey.Pubkey →
    Std.U64 → Bool → Result
    aspis_pool.pair_forest.PoolV1PairForestTerminalBumpHintsV1
  op41
  :
  (Slice Std.U8) → aspis_pool.pair_forest.PoolV1PairForestTerminalBumpHintsV1
    → Result (alloc.vec.Vec Std.U8)
  op42
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result
    (solana_pubkey.Pubkey × Std.U8)
  op43
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result
    (solana_pubkey.Pubkey × Std.U8)
  op44
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result
    (solana_pubkey.Pubkey × Std.U8)
  op45
  {T0 : Type} (coreconvertAsRefT0PathInst : core.convert.AsRef T0
  std.path.Path) :
  T0 → Result (core.result.Result
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
    std.io.error.Error)
  op46
  {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) :
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
    → (Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) →
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore → T0 →
    Result ((core.result.Result aspis_r1_cost_probe.prover.RetriedProof
    aspis_r1_cost_probe.verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  op47
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result
    (solana_pubkey.Pubkey × Std.U8)
  op48
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → (Array Std.U8 32#usize) →
    (Array Std.U8 32#usize) → Result (solana_pubkey.Pubkey × Std.U8)
  op49
  : (Array aspis_core.field.M31 8#usize) → Result (Array Std.U8 32#usize)
  op50
  :
  (Array aspis_core.field.M31 8#usize) → Std.U32 → aspis_core.field.M31 →
    (Array aspis_core.field.M31 8#usize) → Result (Array aspis_core.field.M31
    8#usize)
  op51
  :
  (Array aspis_core.field.M31 8#usize) → (Array aspis_core.field.M31 8#usize)
    → Result (Array aspis_core.field.M31 8#usize)
  op52
  :
  (Array aspis_core.field.M31 8#usize) → (Array aspis_core.field.M31 8#usize)
    → Result (Array aspis_core.field.M31 8#usize)
  op53
  :
  (Array aspis_core.field.M31 8#usize) → Result (core.result.Result Std.U8
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  op54
  :
  (Slice Std.U8) → (Array (Array aspis_core.field.M31 8#usize) 21#usize) →
    Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  op55
  :
  (Slice Std.U8) → Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  op56
  :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  op57
  :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result (core.result.Result (Array Std.U8 1880#usize)
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  op58
  :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
    → Result (core.result.Result (Array Std.U8 320#usize)
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  op59
  :
  aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 →
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1
    → aspis_statement.pool_v1.payment_relation.PoolV1PaymentRelationContextV1
    → aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 →
    Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
    aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1)
  op60
  :
  aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 →
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1
    → aspis_statement.pool_v1.payment_relation.PoolV1PaymentRelationContextV1
    → aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 →
    Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
    aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1)
  op61
  :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 →
    Result (core.result.Result (Array Std.U8 688#usize)
    aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
  op62
  :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1 → Result
    (core.result.Result (Array aspis_core.field.M31 8#usize)
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1)
  op63
  :
  (Array aspis_core.field.M31 8#usize) → Result (core.result.Result
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1)
  op64
  :
  (Array aspis_core.field.M31 8#usize) → (Array aspis_core.field.M31 8#usize)
    → Result (core.result.Result
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1)
  op65
  :
  (Array aspis_core.field.M31 8#usize) → Result (Array aspis_core.field.M31
    8#usize)
  op66
  : Result (serde_json.map.Map String serde_json.value.Value)
  op67
  :
  (serde_json.map.Map String serde_json.value.Value) → String →
    serde_json.value.Value → Result ((Option serde_json.value.Value) ×
    (serde_json.map.Map String serde_json.value.Value))
  op68
  : F64 → Result (Option serde_json.number.Number)
  op69
  : Std.U64 → Result serde_json.number.Number
  op70
  : serde_json.value.Value → Result serde_json.value.Value
  op71
  : serde_json.value.Value → Result (Option Str)
  op72
  : serde_json.value.Value → Result (Option Std.U64)
  op73
  : serde_json.value.Value → Result (Option Bool)
  op74
  :
  Str → Result (core.result.Result solana_pubkey.Pubkey
    solana_pubkey.ParsePubkeyError)
  op75
  : solana_pubkey.Pubkey → Result (Array Std.U8 32#usize)
  op76
  :
  serde_json.value.Value → Result (core.result.Result
    plan.client64_accounts.Accounts diagnostics.Error)
  op77 : solana_pubkey.Pubkey → Result String
  op78 : Bool → Result serde_json.value.Value
  op79
  : (alloc.vec.Vec serde_json.value.Value) → Result serde_json.value.Value
  op80 : String → Result serde_json.value.Value
  op81 : Result Unit
  op82
  :
  serde_json.value.Value → Result (core.result.Result String
    diagnostics.Error)
  op83
  :
  serde_json.value.Value → Result (core.result.Result (alloc.vec.Vec
    serde_json.value.Value) diagnostics.Error)
  op84 : Std.Usize → Result Std.Usize
  op85
  : serde_json.value.Value → Str → Result serde_json.value.Value
  op86 : serde_json.value.Value → Str → Result solana_pubkey.Pubkey
  op87
  :
  (serde_json.map.Map String serde_json.value.Value) → Result
    serde_json.value.Value
  op88 : (Slice Std.U8) → Result String
  op89 : serde_json.number.Number → Result serde_json.value.Value
  op90 : serde_json.value.Value → Str → Result String
  op91 : Str → Result (alloc.vec.Vec Std.U8)
  op92
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result (alloc.vec.Vec
    solana_pubkey.Pubkey)
  op93
  :
  serde_json.value.Value → Result (core.result.Result (alloc.vec.Vec
    serde_json.value.Value) diagnostics.Error)
  op94
  : Result (Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  op95 : std.path.Path → Str → Result std.path.PathBuf
  op96
  : std.path.Path → Result (core.result.Result Unit diagnostics.Error)
  op97
  :
  std.fs.File → (Array Std.U8 212#usize) → Result ((core.result.Result Unit
    diagnostics.Error) × std.fs.File)
  op98
  :
  serde_json.value.Value → Result (core.result.Result std.fs.File
    diagnostics.Error)
  op99
  :
  std.fs.File → Result ((core.result.Result (Array Std.U8 212#usize)
    diagnostics.Error) × std.fs.File)
  op100
  : String → Result (core.result.Result std.fs.File diagnostics.Error)
  op101 : Std.I32 → Result String
  op102
  :
  Str → Result (core.result.Result serde_json.value.Value diagnostics.Error)
  op103 : String → Result Unit
  op104 : serde_json.value.Value → Result String

abbrev Shared0T.Insts.CoreConvertAsRef.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op0 types ext
abbrev U32.Insts.CoreConvertTryFromU64TryFromIntError.try_from [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op1 types ext
abbrev I32.Insts.CoreConvertTryFromU64TryFromIntError.try_from [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op2 types ext
abbrev core.num.U8.from_str_radix [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op3 types ext
abbrev core.num.Usize.div_ceil [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op4 types ext
abbrev core.ops.range.RangeInclusive.contains [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op5 types ext
abbrev core.option.Option.ok_or_else [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op6 types ext
abbrev core.option.Option.Insts.CoreCmpPartialEqOption.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op7 types ext
abbrev core.result.Result.map_err [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op8 types ext
abbrev core.str.Str.len [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op9 types ext
abbrev core.str.Str.is_ascii [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op10 types ext
abbrev Str.Insts.CoreCmpPartialEqStr.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op11 types ext
abbrev Str.Insts.CoreOpsIndexIndex.index [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op12 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.index_mut [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op13 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.index [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op14 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked_mut [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op15 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op16 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_mut [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op17 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op18 types ext
abbrev core.time.Duration.as_secs_f64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op19 types ext
abbrev alloc.string.String.Insts.CoreConvertAsRefOsStr.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op20 types ext
abbrev std.fs.write [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op21 types ext
abbrev std.io.stdio.stdin [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op22 types ext
abbrev std.io.stdio.Stdin.Insts.StdIoRead.read_to_string [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op23 types ext
abbrev std.io.stdio.stderr [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op24 types ext
abbrev std.io.stdio.Stderr.Insts.StdIoWrite.write_all [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op25 types ext
abbrev std.path.Path.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op26 types ext
abbrev std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op27 types ext
abbrev std.process.exit [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op28 types ext
abbrev std.time.Instant.now [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op29 types ext
abbrev std.time.Instant.elapsed [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op30 types ext
abbrev Str.Insts.AllocBorrowToOwnedString.to_owned [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op31 types ext
abbrev alloc.string.String.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op32 types ext
abbrev alloc.string.String.as_str [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op33 types ext
abbrev alloc.string.String.Insts.CoreOpsDerefDerefStr.deref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op34 types ext
abbrev alloc.vec.Vec.Insts.CoreConvertAsRefSlice.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op35 types ext
abbrev aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op36 types ext
abbrev aspis_pool.empty_roots.POOL_V1_PAIR_EMPTY_ROOTS [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op37 types ext
abbrev aspis_pool.history.pool_v1_root_page_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op38 types ext
abbrev aspis_pool.nullifier.pool_v1_pair_forest_nullifier_marker_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op39 types ext
abbrev aspis_pool.pair_forest.pool_v1_pair_forest_terminal_bump_hints_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op40 types ext
abbrev aspis_pool.pair_forest.encode_pair_forest_terminal_instruction_data_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op41 types ext
abbrev aspis_pool.pair_forest.pool_v1_pair_forest_master_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op42 types ext
abbrev aspis_pool.vault.pool_v1_vault_authority_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op43 types ext
abbrev aspis_pool.vault.pool_v1_vault_token_account_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op44 types ext
abbrev aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.open [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op45 types ext
abbrev aspis_r1_cost_probe.RealR1_client.prove_for_proof_accounts [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op46 types ext
abbrev aspis_registry.processor.pool_v1_verifier_registry_v2_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op47 types ext
abbrev aspis_registry.processor.pool_v1_verifier_entry_v2_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op48 types ext
abbrev aspis_statement.atomic_statement.encode_digest_canonical [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op49 types ext
abbrev aspis_statement.pool_v1.format.pool_v1_note_commitment [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op50 types ext
abbrev aspis_statement.pool_v1.format.pool_v1_nullifier [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op51 types ext
abbrev aspis_statement.pool_v1.format.pool_v1_tree_parent [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op52 types ext
abbrev aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op53 types ext
abbrev aspis_statement.pool_v1.pair_forest_accounts.decode_pool_v1_pair_forest_lane_state_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op54 types ext
abbrev aspis_statement.pool_v1.pair_forest_accounts.decode_pool_v1_pair_forest_checkpoint_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op55 types ext
abbrev aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op56 types ext
abbrev aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op57 types ext
abbrev aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_request_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op58 types ext
abbrev aspis_statement.pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op59 types ext
abbrev aspis_statement.pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op60 types ext
abbrev aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op61 types ext
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op62 types ext
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.single_output [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op63 types ext
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.two_outputs [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op64 types ext
abbrev aspis_statement.spend.derive_owner_key [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op65 types ext
abbrev serde_json.map.MapStringValue.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op66 types ext
abbrev serde_json.map.MapStringValue.insert [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op67 types ext
abbrev serde_json.number.Number.from_f64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op68 types ext
abbrev serde_json.number.Number.Insts.CoreConvertFromU64.from [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op69 types ext
abbrev serde_json.value.Value.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op70 types ext
abbrev serde_json.value.Value.as_str [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op71 types ext
abbrev serde_json.value.Value.as_u64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op72 types ext
abbrev serde_json.value.Value.as_bool [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op73 types ext
abbrev solana_pubkey.Pubkey.Insts.CoreStrTraitsFromStrParsePubkeyError.from_str [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op74 types ext
abbrev solana_pubkey.Pubkey.to_bytes [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op75 types ext
abbrev plan.client64_accounts.Accounts.parse [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op76 types ext
abbrev pubkey_text [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op77 types ext
abbrev json_bool [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op78 types ext
abbrev json_array [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op79 types ext
abbrev json_string [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op80 types ext
abbrev diagnostics.initialize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op81 types ext
abbrev value_text [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op82 types ext
abbrev public_array [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op83 types ext
abbrev parent_capacity [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op84 types ext
abbrev public_field [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op85 types ext
abbrev plan.pk [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op86 types ext
abbrev json_object [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op87 types ext
abbrev hex [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op88 types ext
abbrev json_number [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op89 types ext
abbrev public_text [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op90 types ext
abbrev unhex [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op91 types ext
abbrev public_lanes [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op92 types ext
abbrev json_into_array [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op93 types ext
abbrev client_hash [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op94 types ext
abbrev path_join [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op95 types ext
abbrev create_private_directory [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op96 types ext
abbrev wallet.return_record [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op97 types ext
abbrev wallet.output_channel [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op98 types ext
abbrev wallet_read_record [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op99 types ext
abbrev wallet_open_channel [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op100 types ext
abbrev wallet_fd_path [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op101 types ext
abbrev parse_request [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op102 types ext
abbrev print_json [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op103 types ext
abbrev render_json [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op104 types ext
end PV_UC5_Entry
