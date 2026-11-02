import Aeneas
import PVUCBoundEntry.Types
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_UC_BoundEntry

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
  {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F
  Clause0_Item B) :
  Self → F → Result (core.iter.adapters.map.Map Self F)
  op4
  {B : Type} {I : Type} {F : Type} {Clause0_Item : Type}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I
  Clause0_Item) (opsfunctionFnMutFTupleClause0_ItemBInst :
  core.ops.function.FnMut F Clause0_Item B) :
  (core.iter.adapters.map.Map I F) → Result ((Option B) ×
    (core.iter.adapters.map.Map I F))
  op5
  :
  core.num.error.ParseIntError → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  op6
  :
  Str → Std.U32 → Result (core.result.Result Std.U8
    core.num.error.ParseIntError)
  op7 : Std.Usize → Std.Usize → Result Std.Usize
  op8
  {Idx : Type} {U : Type} (cmpPartialOrdInst : core.cmp.PartialOrd Idx Idx)
  (cmpPartialOrdInst1 : core.cmp.PartialOrd Idx U) (cmpPartialOrdInst2 :
  core.cmp.PartialOrd U Idx) :
  (core.ops.range.RangeInclusive Idx) → U → Result Bool
  op9
  {T : Type} {E : Type} {F : Type} (opsfunctionFnOnceFTupleEInst :
  core.ops.function.FnOnce F Unit E) :
  (Option T) → F → Result (core.result.Result T E)
  op10
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
  (Option T) → (Option T) → Result Bool
  op11
  {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) :
  (core.result.Result T E) → O → Result (core.result.Result T F)
  op12 : Str → Result Std.Usize
  op13 : Str → Result Bool
  op14 : Str → Str → Result Bool
  op15
  {I : Type} {Clause0_Output : Type}
  (sliceindexSliceIndexIStrClause0_OutputInst : core.slice.index.SliceIndex I
  Str Clause0_Output) :
  Str → I → Result Clause0_Output
  op16
  : (core.ops.range.Range Std.Usize) → Str → Result (Str × (Str → Str))
  op17
  : (core.ops.range.Range Std.Usize) → Str → Result Str
  op18
  :
  (core.ops.range.Range Std.Usize) → (MutRawPtr Str) → Result (MutRawPtr
    Str)
  op19
  :
  (core.ops.range.Range Std.Usize) → (ConstRawPtr Str) → Result
    (ConstRawPtr Str)
  op20
  :
  (core.ops.range.Range Std.Usize) → Str → Result ((Option Str) × (Option
    Str → Str))
  op21
  : (core.ops.range.Range Std.Usize) → Str → Result (Option Str)
  op22 : core.time.Duration → Result F64
  op23 : Result std.backtrace.Backtrace
  op24
  : std.backtrace.Backtrace → Result std.backtrace.BacktraceStatus
  op25
  {K : Type} {V : Type} (coreconvertAsRefKOsStrInst : core.convert.AsRef K
  std.ffi.os_str.OsStr) (coreconvertAsRefVOsStrInst : core.convert.AsRef V
  std.ffi.os_str.OsStr) :
  K → V → Result Unit
  op26
  : Str → Result std.ffi.os_str.OsStr
  op27
  : String → Result std.ffi.os_str.OsStr
  op28
  {P : Type} {C : Type} (coreconvertAsRefPPathInst : core.convert.AsRef P
  std.path.Path) (coreconvertAsRefCSliceU8Inst : core.convert.AsRef C (Slice
  Std.U8)) :
  P → C → Result (core.result.Result Unit std.io.error.Error)
  op29
  {P : Type} (coreconvertAsRefPPathInst : core.convert.AsRef P std.path.Path) :
  P → Result (core.result.Result std.fs.File std.io.error.Error)
  op30
  : std.fs.File → Result (core.result.Result Unit std.io.error.Error)
  op31
  {Self : Type} (ReadInst : std.io.Read Self) :
  Self → (Slice Std.U8) → Result ((core.result.Result Unit
    std.io.error.Error) × Self × (Slice Std.U8))
  op32
  :
  std.fs.File → String → Result ((core.result.Result Std.Usize
    std.io.error.Error) × std.fs.File × String)
  op33
  :
  std.fs.File → (Slice Std.U8) → Result ((core.result.Result Std.Usize
    std.io.error.Error) × std.fs.File × (Slice Std.U8))
  op34
  {Self : Type} (WriteInst : std.io.Write Self) :
  Self → (Slice Std.U8) → Result ((core.result.Result Unit
    std.io.error.Error) × Self)
  op35
  :
  std.fs.File → Result ((core.result.Result Unit std.io.error.Error) ×
    std.fs.File)
  op36
  :
  std.fs.File → (Slice Std.U8) → Result ((core.result.Result Std.Usize
    std.io.error.Error) × std.fs.File)
  op37 : Result std.fs.OpenOptions
  op38
  :
  std.fs.OpenOptions → Bool → Result (std.fs.OpenOptions ×
    (std.fs.OpenOptions → std.fs.OpenOptions))
  op39
  :
  std.fs.OpenOptions → Bool → Result (std.fs.OpenOptions ×
    (std.fs.OpenOptions → std.fs.OpenOptions))
  op40
  {P : Type} (coreconvertAsRefPPathInst : core.convert.AsRef P std.path.Path) :
  std.fs.OpenOptions → P → Result (core.result.Result std.fs.File
    std.io.error.Error)
  op41
  {Self : Type} (ReadInst : std.io.Read Self) :
  Self → String → Result ((core.result.Result Std.Usize std.io.error.Error)
    × Self × String)
  op42 : Result std.io.stdio.Stdin
  op43
  :
  std.io.stdio.Stdin → String → Result ((core.result.Result Std.Usize
    std.io.error.Error) × std.io.stdio.Stdin × String)
  op44 : Result std.io.stdio.Stderr
  op45
  :
  std.io.stdio.Stderr → (Slice Std.U8) → Result ((core.result.Result Unit
    std.io.error.Error) × std.io.stdio.Stderr)
  op46
  :
  std.fs.OpenOptions → Std.U32 → Result (std.fs.OpenOptions ×
    (std.fs.OpenOptions → std.fs.OpenOptions))
  op47
  {S : Type} (coreconvertAsRefSOsStrInst : core.convert.AsRef S
  std.ffi.os_str.OsStr) :
  S → Result std.path.Path
  op48
  : String → Result std.path.Path
  op49
  : std.path.PathBuf → Result std.path.Path
  op50 : Std.I32 → Result Never
  op51 : Result std.time.Instant
  op52 : std.time.Instant → Result core.time.Duration
  op53 : Str → Result String
  op54
  :
  alloc.string.FromUtf8Error → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  op55 : Result String
  op56
  :
  (alloc.vec.Vec Std.U8) → Result (core.result.Result String
    alloc.string.FromUtf8Error)
  op57 : String → Result Str
  op58
  : String → Result Str
  op59
  {T : Type} (corefmtDisplayInst : core.fmt.Display T) : T → Result String
  op60
  {T : Type} (A : Type) : (alloc.vec.Vec T) → Result (Slice T)
  op61
  : aspis_core.field.M31 → aspis_core.field.M31 → Result Bool
  op62
  : Result (Array (Array aspis_core.field.M31 8#usize) 21#usize)
  op63
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Std.U64 → Result
    (solana_pubkey.Pubkey × Std.U8)
  op64
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → (Array Std.U8 32#usize) →
    Result (core.result.Result (solana_pubkey.Pubkey × (Array Std.U8
    32#usize)) solana_program_error.ProgramError)
  op65
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → solana_pubkey.Pubkey →
    Std.U64 → Bool → Result
    aspis_pool.pair_forest.PoolV1PairForestTerminalBumpHintsV1
  op66
  :
  (Slice Std.U8) → aspis_pool.pair_forest.PoolV1PairForestTerminalBumpHintsV1
    → Result (alloc.vec.Vec Std.U8)
  op67
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result
    (solana_pubkey.Pubkey × Std.U8)
  op68
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Std.U8 → Result
    (core.result.Result (solana_pubkey.Pubkey × Std.U8)
    solana_program_error.ProgramError)
  op69
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result
    (solana_pubkey.Pubkey × Std.U8)
  op70
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result
    (solana_pubkey.Pubkey × Std.U8)
  op71
  {T0 : Type} (coreconvertAsRefT0PathInst : core.convert.AsRef T0
  std.path.Path) :
  T0 → Result (core.result.Result
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
    std.io.error.Error)
  op72
  {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) :
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
    → (Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) →
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore → T0 →
    Result ((core.result.Result aspis_r1_cost_probe.prover.RetriedProof
    aspis_r1_cost_probe.verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  op73
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result
    (solana_pubkey.Pubkey × Std.U8)
  op74
  :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → (Array Std.U8 32#usize) →
    (Array Std.U8 32#usize) → Result (solana_pubkey.Pubkey × Std.U8)
  op75
  : (Array aspis_core.field.M31 8#usize) → Result (Array Std.U8 32#usize)
  op76
  :
  (Array aspis_core.field.M31 8#usize) → Std.U32 → aspis_core.field.M31 →
    (Array aspis_core.field.M31 8#usize) → Result (Array aspis_core.field.M31
    8#usize)
  op77
  :
  (Array aspis_core.field.M31 8#usize) → (Array aspis_core.field.M31 8#usize)
    → Result (Array aspis_core.field.M31 8#usize)
  op78
  :
  (Array aspis_core.field.M31 8#usize) → (Array aspis_core.field.M31 8#usize)
    → Result (Array aspis_core.field.M31 8#usize)
  op79
  :
  (Array aspis_core.field.M31 8#usize) → Result (core.result.Result Std.U8
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  op80
  :
  (Slice Std.U8) → (Array (Array aspis_core.field.M31 8#usize) 21#usize) →
    Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  op81
  :
  (Slice Std.U8) → Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
    aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  op82
  :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  op83
  :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result (core.result.Result (Array Std.U8 1880#usize)
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  op84
  :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
    → Result (core.result.Result (Array Std.U8 320#usize)
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  op85
  :
  aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 →
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1
    → aspis_statement.pool_v1.payment_relation.PoolV1PaymentRelationContextV1
    → aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 →
    Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
    aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1)
  op86
  :
  aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 →
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1
    → aspis_statement.pool_v1.payment_relation.PoolV1PaymentRelationContextV1
    → aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 →
    Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
    aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1)
  op87
  :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 →
    Result (core.result.Result (Array Std.U8 688#usize)
    aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1)
  op88
  :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1 → Result
    (core.result.Result (Array aspis_core.field.M31 8#usize)
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1)
  op89
  :
  (Array aspis_core.field.M31 8#usize) → Result (core.result.Result
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1)
  op90
  :
  (Array aspis_core.field.M31 8#usize) → (Array aspis_core.field.M31 8#usize)
    → Result (core.result.Result
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1)
  op91
  :
  (Array aspis_core.field.M31 8#usize) → Result (Array aspis_core.field.M31
    8#usize)
  op92
  {T : Type} (serde_coredeDeserializeInst : serde_core.de.Deserialize T) :
  Str → Result (core.result.Result T serde_json.error.Error)
  op93
  : Result (serde_json.map.Map String serde_json.value.Value)
  op94
  :
  (serde_json.map.Map String serde_json.value.Value) → String →
    serde_json.value.Value → Result ((Option serde_json.value.Value) ×
    (serde_json.map.Map String serde_json.value.Value))
  op95
  : F64 → Result (Option serde_json.number.Number)
  op96
  : Std.U64 → Result serde_json.number.Number
  op97
  {D : Type} {Clause0_Error : Type} (serde_coredeDeserializerInst :
  serde_core.de.Deserializer D Clause0_Error) :
  D → Result (core.result.Result serde_json.value.Value Clause0_Error)
  op98
  : serde_json.value.Value → Result serde_json.value.Value
  op99
  : serde_json.value.Value → Result (Option Str)
  op100
  : serde_json.value.Value → Result (Option Std.U64)
  op101
  : serde_json.value.Value → Result (Option Bool)
  op102
  :
  solana_program_error.ProgramError → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  op103
  :
  solana_pubkey.ParsePubkeyError → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  op104
  :
  Str → Result (core.result.Result solana_pubkey.Pubkey
    solana_pubkey.ParsePubkeyError)
  op105
  : solana_pubkey.Pubkey → Result (Array Std.U8 32#usize)
  op106
  :
  solana_pubkey.Pubkey → core.fmt.Formatter → Result ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)
  op107
  :
  serde_json.value.Value → Result (core.result.Result
    plan.client64_accounts.Accounts diagnostics.Error)
  op108 : Bool → Result serde_json.value.Value
  op109
  : (alloc.vec.Vec serde_json.value.Value) → Result serde_json.value.Value
  op110 : String → Result serde_json.value.Value
  op111 : Result Unit
  op112
  :
  serde_json.value.Value → Result (core.result.Result String
    diagnostics.Error)
  op113
  :
  serde_json.value.Value → Result (core.result.Result (alloc.vec.Vec
    serde_json.value.Value) diagnostics.Error)
  op114
  : serde_json.value.Value → Str → Result serde_json.value.Value
  op115 : serde_json.value.Value → Str → Result String
  op116
  :
  (serde_json.map.Map String serde_json.value.Value) → Result
    serde_json.value.Value
  op117 : serde_json.number.Number → Result serde_json.value.Value
  op118
  :
  serde_json.value.Value → Result (core.result.Result (alloc.vec.Vec
    serde_json.value.Value) diagnostics.Error)
  op119
  : Result (Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  op120 : std.path.Path → Str → Result std.path.PathBuf
  op121
  : std.path.Path → Result (core.result.Result Unit diagnostics.Error)
  op122 : Std.I32 → Result String
  op123 : serde_json.value.Value → Result Unit

abbrev Shared0T.Insts.CoreConvertAsRef.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op0 types ext
abbrev U32.Insts.CoreConvertTryFromU64TryFromIntError.try_from [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op1 types ext
abbrev I32.Insts.CoreConvertTryFromU64TryFromIntError.try_from [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op2 types ext
abbrev core.iter.traits.iterator.Iterator.map.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op3 types ext
abbrev core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op4 types ext
abbrev core.num.error.ParseIntError.Insts.CoreFmtDebug.fmt [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op5 types ext
abbrev core.num.U8.from_str_radix [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op6 types ext
abbrev core.num.Usize.div_ceil [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op7 types ext
abbrev core.ops.range.RangeInclusive.contains [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op8 types ext
abbrev core.option.Option.ok_or_else [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op9 types ext
abbrev core.option.Option.Insts.CoreCmpPartialEqOption.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op10 types ext
abbrev core.result.Result.map_err [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op11 types ext
abbrev core.str.Str.len [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op12 types ext
abbrev core.str.Str.is_ascii [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op13 types ext
abbrev Str.Insts.CoreCmpPartialEqStr.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op14 types ext
abbrev Str.Insts.CoreOpsIndexIndex.index [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op15 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.index_mut [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op16 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.index [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op17 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked_mut [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op18 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_unchecked [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op19 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get_mut [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op20 types ext
abbrev core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexStrStr.get [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op21 types ext
abbrev core.time.Duration.as_secs_f64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op22 types ext
abbrev std.backtrace.Backtrace.capture [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op23 types ext
abbrev std.backtrace.Backtrace.status [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op24 types ext
abbrev std.env.set_var [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op25 types ext
abbrev Str.Insts.CoreConvertAsRefOsStr.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op26 types ext
abbrev alloc.string.String.Insts.CoreConvertAsRefOsStr.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op27 types ext
abbrev std.fs.write [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op28 types ext
abbrev std.fs.File.open [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op29 types ext
abbrev std.fs.File.sync_all [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op30 types ext
abbrev std.io.Read.read_exact.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op31 types ext
abbrev std.fs.File.Insts.StdIoRead.read_to_string [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op32 types ext
abbrev std.fs.File.Insts.StdIoRead.read [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op33 types ext
abbrev std.io.Write.write_all.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op34 types ext
abbrev std.fs.File.Insts.StdIoWrite.flush [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op35 types ext
abbrev std.fs.File.Insts.StdIoWrite.write [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op36 types ext
abbrev std.fs.OpenOptions.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op37 types ext
abbrev std.fs.OpenOptions.write [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op38 types ext
abbrev std.fs.OpenOptions.create_new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op39 types ext
abbrev std.fs.OpenOptions.open [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op40 types ext
abbrev std.io.Read.read_to_string.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op41 types ext
abbrev std.io.stdio.stdin [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op42 types ext
abbrev std.io.stdio.Stdin.Insts.StdIoRead.read_to_string [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op43 types ext
abbrev std.io.stdio.stderr [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op44 types ext
abbrev std.io.stdio.Stderr.Insts.StdIoWrite.write_all [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op45 types ext
abbrev std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op46 types ext
abbrev std.path.Path.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op47 types ext
abbrev alloc.string.String.Insts.CoreConvertAsRefPath.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op48 types ext
abbrev std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op49 types ext
abbrev std.process.exit [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op50 types ext
abbrev std.time.Instant.now [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op51 types ext
abbrev std.time.Instant.elapsed [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op52 types ext
abbrev Str.Insts.AllocBorrowToOwnedString.to_owned [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op53 types ext
abbrev alloc.string.FromUtf8Error.Insts.CoreFmtDebug.fmt [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op54 types ext
abbrev alloc.string.String.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op55 types ext
abbrev alloc.string.String.from_utf8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op56 types ext
abbrev alloc.string.String.as_str [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op57 types ext
abbrev alloc.string.String.Insts.CoreOpsDerefDerefStr.deref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op58 types ext
abbrev alloc.string.ToString.Blanket.to_string [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op59 types ext
abbrev alloc.vec.Vec.Insts.CoreConvertAsRefSlice.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op60 types ext
abbrev aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op61 types ext
abbrev aspis_pool.empty_roots.POOL_V1_PAIR_EMPTY_ROOTS [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op62 types ext
abbrev aspis_pool.history.pool_v1_root_page_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op63 types ext
abbrev aspis_pool.nullifier.pool_v1_pair_forest_nullifier_marker_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op64 types ext
abbrev aspis_pool.pair_forest.pool_v1_pair_forest_terminal_bump_hints_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op65 types ext
abbrev aspis_pool.pair_forest.encode_pair_forest_terminal_instruction_data_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op66 types ext
abbrev aspis_pool.pair_forest.pool_v1_pair_forest_master_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op67 types ext
abbrev aspis_pool.pair_forest.pool_v1_pair_forest_lane_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op68 types ext
abbrev aspis_pool.vault.pool_v1_vault_authority_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op69 types ext
abbrev aspis_pool.vault.pool_v1_vault_token_account_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op70 types ext
abbrev aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.open [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op71 types ext
abbrev aspis_r1_cost_probe.RealR1_client.prove_for_proof_accounts [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op72 types ext
abbrev aspis_registry.processor.pool_v1_verifier_registry_v2_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op73 types ext
abbrev aspis_registry.processor.pool_v1_verifier_entry_v2_address [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op74 types ext
abbrev aspis_statement.atomic_statement.encode_digest_canonical [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op75 types ext
abbrev aspis_statement.pool_v1.format.pool_v1_note_commitment [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op76 types ext
abbrev aspis_statement.pool_v1.format.pool_v1_nullifier [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op77 types ext
abbrev aspis_statement.pool_v1.format.pool_v1_tree_parent [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op78 types ext
abbrev aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op79 types ext
abbrev aspis_statement.pool_v1.pair_forest_accounts.decode_pool_v1_pair_forest_lane_state_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op80 types ext
abbrev aspis_statement.pool_v1.pair_forest_accounts.decode_pool_v1_pair_forest_checkpoint_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op81 types ext
abbrev aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op82 types ext
abbrev aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op83 types ext
abbrev aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_request_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op84 types ext
abbrev aspis_statement.pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op85 types ext
abbrev aspis_statement.pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op86 types ext
abbrev aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op87 types ext
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op88 types ext
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.single_output [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op89 types ext
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.two_outputs [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op90 types ext
abbrev aspis_statement.spend.derive_owner_key [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op91 types ext
abbrev serde_json.de.from_str [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op92 types ext
abbrev serde_json.map.MapStringValue.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op93 types ext
abbrev serde_json.map.MapStringValue.insert [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op94 types ext
abbrev serde_json.number.Number.from_f64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op95 types ext
abbrev serde_json.number.Number.Insts.CoreConvertFromU64.from [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op96 types ext
abbrev serde_json.value.Value.Insts.Serde_coreDeDeserialize.deserialize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op97 types ext
abbrev serde_json.value.Value.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op98 types ext
abbrev serde_json.value.Value.as_str [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op99 types ext
abbrev serde_json.value.Value.as_u64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op100 types ext
abbrev serde_json.value.Value.as_bool [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op101 types ext
abbrev solana_program_error.ProgramError.Insts.CoreFmtDebug.fmt [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op102 types ext
abbrev solana_pubkey.ParsePubkeyError.Insts.CoreFmtDebug.fmt [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op103 types ext
abbrev solana_pubkey.Pubkey.Insts.CoreStrTraitsFromStrParsePubkeyError.from_str [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op104 types ext
abbrev solana_pubkey.Pubkey.to_bytes [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op105 types ext
abbrev solana_pubkey.Pubkey.Insts.CoreFmtDisplay.fmt [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op106 types ext
abbrev plan.client64_accounts.Accounts.parse [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op107 types ext
abbrev json_bool [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op108 types ext
abbrev json_array [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op109 types ext
abbrev json_string [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op110 types ext
abbrev diagnostics.install_literal_panic_hook [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op111 types ext
abbrev value_text [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op112 types ext
abbrev public_array [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op113 types ext
abbrev public_field [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op114 types ext
abbrev public_text [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op115 types ext
abbrev json_object [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op116 types ext
abbrev json_number [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op117 types ext
abbrev json_into_array [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op118 types ext
abbrev client_hash [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op119 types ext
abbrev path_join [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op120 types ext
abbrev create_private_directory [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op121 types ext
abbrev wallet_fd_path [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op122 types ext
abbrev print_json [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op123 types ext

end PV_UC_BoundEntry
