import Aeneas
open Aeneas Aeneas.Std Result ControlFlow
noncomputable section
namespace ProverRwRngNativeBody
class TypeLeaves where
  t0 : Type
  t1 : Type
  t2 : Type
  t3 : Type
  t4 : Type
  t5 : Type
  t6 : Type
  t7 :
  Type
  t8 : Type
  t9 : Type
  t10 : Type
  t11 : Type
  t12 : Type
  t13 : Type
  t14 : Type
  t15 (H : Type) : Type
variable [TypeLeaves]
abbrev std.io.error.Error := @TypeLeaves.t0 _
abbrev std.path.PathBuf := @TypeLeaves.t1 _
abbrev aspis_core.circle.SecureCirclePoint := @TypeLeaves.t2 _
abbrev aspis_core.r0.Error := @TypeLeaves.t3 _
abbrev aspis_core.state_only_prefix.r0.Error := @TypeLeaves.t4 _
abbrev aspis_core.state_only_prefix.r0.Challenges := @TypeLeaves.t5 _
abbrev aspis_prover.state_only_hiding.StateOnlyMaskMaterial := @TypeLeaves.t6 _
abbrev aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 := @TypeLeaves.t7 _
abbrev aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public := @TypeLeaves.t8 _
abbrev aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1 := @TypeLeaves.t9 _
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 := @TypeLeaves.t10 _
abbrev host_commitment.EncodingDomain := @TypeLeaves.t11 _
abbrev host_commitment.Commitment := @TypeLeaves.t12 _
abbrev host_commitment.PrivateSalts := @TypeLeaves.t13 _
abbrev r1_wire.Error := @TypeLeaves.t14 _
abbrev host_wire.SemanticTranscript := @TypeLeaves.t15 _

/-- [core::io::error::ErrorKind]
    Source: '/rustc/library/core/src/io/error.rs', lines 45:0-45:18
    Name pattern: [core::io::error::ErrorKind]
    Visibility: public -/
@[rust_type "core::io::error::ErrorKind"]
inductive core.io.error.ErrorKind where
| NotFound : core.io.error.ErrorKind
| PermissionDenied : core.io.error.ErrorKind
| ConnectionRefused : core.io.error.ErrorKind
| ConnectionReset : core.io.error.ErrorKind
| HostUnreachable : core.io.error.ErrorKind
| NetworkUnreachable : core.io.error.ErrorKind
| ConnectionAborted : core.io.error.ErrorKind
| NotConnected : core.io.error.ErrorKind
| AddrInUse : core.io.error.ErrorKind
| AddrNotAvailable : core.io.error.ErrorKind
| NetworkDown : core.io.error.ErrorKind
| BrokenPipe : core.io.error.ErrorKind
| AlreadyExists : core.io.error.ErrorKind
| WouldBlock : core.io.error.ErrorKind
| NotADirectory : core.io.error.ErrorKind
| IsADirectory : core.io.error.ErrorKind
| DirectoryNotEmpty : core.io.error.ErrorKind
| ReadOnlyFilesystem : core.io.error.ErrorKind
| FilesystemLoop : core.io.error.ErrorKind
| StaleNetworkFileHandle : core.io.error.ErrorKind
| InvalidInput : core.io.error.ErrorKind
| InvalidData : core.io.error.ErrorKind
| TimedOut : core.io.error.ErrorKind
| WriteZero : core.io.error.ErrorKind
| StorageFull : core.io.error.ErrorKind
| NotSeekable : core.io.error.ErrorKind
| QuotaExceeded : core.io.error.ErrorKind
| FileTooLarge : core.io.error.ErrorKind
| ResourceBusy : core.io.error.ErrorKind
| ExecutableFileBusy : core.io.error.ErrorKind
| Deadlock : core.io.error.ErrorKind
| CrossesDevices : core.io.error.ErrorKind
| TooManyLinks : core.io.error.ErrorKind
| InvalidFilename : core.io.error.ErrorKind
| ArgumentListTooLong : core.io.error.ErrorKind
| Interrupted : core.io.error.ErrorKind
| Unsupported : core.io.error.ErrorKind
| UnexpectedEof : core.io.error.ErrorKind
| OutOfMemory : core.io.error.ErrorKind
| InProgress : core.io.error.ErrorKind
| Other : core.io.error.ErrorKind
| Uncategorized : core.io.error.ErrorKind

/-- Trait declaration: [aspis_core::digest::Digest32]
    Source: 'crates/aspis-core/src/digest.rs', lines 6:0-6:24
    Name pattern: [aspis_core::digest::Digest32]
    Visibility: public -/
@[rust_trait "aspis_core::digest::Digest32"
  (parentClauses := ["coremarkerCopyInst"])]
structure aspis_core.digest.Digest32 (Self : Type) where
  coremarkerCopyInst : core.marker.Copy Self
  digest : Self → (Slice (Slice Std.U8)) → Result (Array Std.U8 32#usize)

/-- [aspis_core::digest::LegacyHashFn]
    Source: 'crates/aspis-core/src/digest.rs', lines 13:0-13:23
    Name pattern: [aspis_core::digest::LegacyHashFn]
    Visibility: public -/
@[reducible, rust_type "aspis_core::digest::LegacyHashFn"]
def aspis_core.digest.LegacyHashFn :=
  Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)

/-- [aspis_core::field::M31]
    Source: 'crates/aspis-core/src/field.rs', lines 23:0-23:14
    Name pattern: [aspis_core::field::M31]
    Visibility: public -/
@[reducible, rust_type "aspis_core::field::M31"]
def aspis_core.field.M31 := Std.U32

/-- [aspis_core::field::CM31]
    Source: 'crates/aspis-core/src/field.rs', lines 255:0-255:15
    Name pattern: [aspis_core::field::CM31]
    Visibility: public -/
@[rust_type "aspis_core::field::CM31"]
structure aspis_core.field.CM31 where
  a : aspis_core.field.M31
  b : aspis_core.field.M31

/-- [aspis_core::field::QM31]
    Source: 'crates/aspis-core/src/field.rs', lines 432:0-432:15
    Name pattern: [aspis_core::field::QM31]
    Visibility: public -/
@[rust_type "aspis_core::field::QM31"]
structure aspis_core.field.QM31 where
  c0 : aspis_core.field.CM31
  c1 : aspis_core.field.CM31

/-- [aspis_core::field::wide_exact::WideExact]
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 28:0-28:20
    Name pattern: [aspis_core::field::wide_exact::WideExact]
    Visibility: public -/
@[rust_type "aspis_core::field::wide_exact::WideExact"]
structure aspis_core.field.wide_exact.WideExact where
  c0 : aspis_core.field.QM31
  c1 : aspis_core.field.QM31

/-- [aspis_core::state_only_hiding::StateOnlyHidingContext]
    Source: 'crates/aspis-core/src/state_only_hiding.rs', lines 101:0-101:33
    Name pattern: [aspis_core::state_only_hiding::StateOnlyHidingContext]
    Visibility: public -/
@[rust_type "aspis_core::state_only_hiding::StateOnlyHidingContext"]
structure aspis_core.state_only_hiding.StateOnlyHidingContext where
  statement_digest : Array Std.U8 32#usize
  mask_nonce : Array Std.U8 32#usize
  mask_layout_fingerprint : Std.U64
  layout_factor_fingerprint : Std.U64

/-- [zeroize::Zeroizing]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.1/src/lib.rs', lines 621:0-621:32
    Name pattern: [zeroize::Zeroizing]
    Visibility: public -/
@[reducible, rust_type "zeroize::Zeroizing"]
def zeroize.Zeroizing (Z : Type) := Z

/-- [aspis_prover::state_only_entropy::StateOnlyAttemptSecrets]
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 85:0-85:34
    Name pattern: [aspis_prover::state_only_entropy::StateOnlyAttemptSecrets]
    Visibility: public -/
@[rust_type "aspis_prover::state_only_entropy::StateOnlyAttemptSecrets"]
structure aspis_prover.state_only_entropy.StateOnlyAttemptSecrets where
  mask_nonce : Array Std.U8 32#usize
  field_mask_entropy : zeroize.Zeroizing (Array Std.U8 32#usize)
  leaf_salt_seed : zeroize.Zeroizing (Array Std.U8 32#usize)

/-- Trait declaration: [zeroize::Zeroize]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.1/src/lib.rs', lines 272:0-272:17
    Name pattern: [zeroize::Zeroize]
    Visibility: public -/
@[rust_trait "zeroize::Zeroize"]
structure zeroize.Zeroize (Self : Type) where
  zeroize : Self → Result Self

/-- Trait declaration: [zeroize::DefaultIsZeroes]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.1/src/lib.rs', lines 282:0-282:49
    Name pattern: [zeroize::DefaultIsZeroes]
    Visibility: public -/
@[rust_trait "zeroize::DefaultIsZeroes"
  (parentClauses := ["coremarkerCopyInst", "coredefaultDefaultInst"])]
structure zeroize.DefaultIsZeroes (Self : Type) where
  coremarkerCopyInst : core.marker.Copy Self
  coredefaultDefaultInst : core.default.Default Self

/-- [aspis_prover::state_only_entropy::ReservedStateOnlyAttemptSecrets]
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 94:0-94:42
    Name pattern: [aspis_prover::state_only_entropy::ReservedStateOnlyAttemptSecrets]
    Visibility: public -/
@[rust_type
  "aspis_prover::state_only_entropy::ReservedStateOnlyAttemptSecrets"]
structure aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets where
  mask_nonce : Array Std.U8 32#usize
  precommit_binding : Array Std.U8 32#usize
  reserved_context : aspis_core.state_only_hiding.StateOnlyHidingContext
  leaf_salt_seed : zeroize.Zeroizing (Array Std.U8 32#usize)
  source_mask_seed : zeroize.Zeroizing (Array Std.U8 32#usize)

/-- Trait declaration: [aspis_prover::state_only_hiding::StateOnlyMaskNonceStore]
    Source: 'crates/aspis-prover/src/state_only_hiding.rs', lines 62:0-62:33
    Name pattern: [aspis_prover::state_only_hiding::StateOnlyMaskNonceStore]
    Visibility: public -/
@[rust_trait "aspis_prover::state_only_hiding::StateOnlyMaskNonceStore"]
structure aspis_prover.state_only_hiding.StateOnlyMaskNonceStore (Self : Type)
  where
  «reserve» : Self → (Array Std.U8 32#usize) → (Array Std.U8 32#usize)
    → Result (Bool × Self)

/-- [aspis_prover::state_only_hiding::StateOnlyMaskBuildError]
    Source: 'crates/aspis-prover/src/state_only_hiding.rs', lines 51:0-51:32
    Name pattern: [aspis_prover::state_only_hiding::StateOnlyMaskBuildError]
    Visibility: public -/
@[rust_type
  "aspis_prover::state_only_hiding::StateOnlyMaskBuildError"]
inductive aspis_prover.state_only_hiding.StateOnlyMaskBuildError where
| ZeroPrivateEntropy : aspis_prover.state_only_hiding.StateOnlyMaskBuildError
| ReusedMaskNonce : aspis_prover.state_only_hiding.StateOnlyMaskBuildError
| MaskSampleExhausted : aspis_prover.state_only_hiding.StateOnlyMaskBuildError
| TraceShape : aspis_prover.state_only_hiding.StateOnlyMaskBuildError
| Layout : aspis_prover.state_only_hiding.StateOnlyMaskBuildError

/-- [aspis_prover::state_only_entropy::PreReservedNonce]
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 459:0-459:23
    Name pattern: [aspis_prover::state_only_entropy::PreReservedNonce] -/
@[rust_type "aspis_prover::state_only_entropy::PreReservedNonce"]
structure aspis_prover.state_only_entropy.PreReservedNonce where
  statement_digest : Array Std.U8 32#usize
  mask_nonce : Array Std.U8 32#usize
  consumed : Bool

/-- [aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore]
    Source: 'crates/aspis-prover/src/state_only_entropy.rs', lines 924:0-924:41
    Name pattern: [aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore]
    Visibility: public -/
@[rust_type "aspis_prover::state_only_entropy::DurableStateOnlyMaskNonceStore"]
structure aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore where
  directory : std.path.PathBuf
  last_error : Option core.io.error.ErrorKind

/-- [aspis_prover::state_only_hiding::AppliedStateOnlyMasks]
    Source: 'crates/aspis-prover/src/state_only_hiding.rs', lines 110:0-110:32
    Name pattern: [aspis_prover::state_only_hiding::AppliedStateOnlyMasks]
    Visibility: public -/
@[rust_type "aspis_prover::state_only_hiding::AppliedStateOnlyMasks"]
structure aspis_prover.state_only_hiding.AppliedStateOnlyMasks where
  mask_only_c1 : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize
  g : alloc.vec.Vec aspis_core.field.QM31
  h1_padding : alloc.vec.Vec aspis_core.field.QM31
  mask_nonce : Array Std.U8 32#usize

/-- [aspis_statement::state_only_trace::StateOnlyTraceFoundation]
    Source: 'crates/aspis-statement/src/state_only_trace.rs', lines 75:0-75:35
    Name pattern: [aspis_statement::state_only_trace::StateOnlyTraceFoundation]
    Visibility: public -/
@[rust_type "aspis_statement::state_only_trace::StateOnlyTraceFoundation"]
structure aspis_statement.state_only_trace.StateOnlyTraceFoundation where
  c1 : Array (alloc.vec.Vec aspis_core.field.M31) 16#usize

/-- [aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestMergedC1CompilationV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_trace.rs', lines 87:0-87:48
    Name pattern: [aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestMergedC1CompilationV1]
    Visibility: public -/
@[rust_type
  "aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestMergedC1CompilationV1"]
structure aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  where
  trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1
  semantic_c1 : aspis_statement.state_only_trace.StateOnlyTraceFoundation
  public_statement :
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

/-- Trait declaration: [aspis_r1_cost_probe::host_semantic::Commitments]
    Source: 'crates/aspis-r1-cost-probe/src/host_semantic.rs', lines 8:4-11:5
    Visibility: public -/
structure host_semantic.Commitments (Self : Type) where
  c1 : Self → (Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) →
    (Array aspis_core.field.QM31 1024#usize) → Result ((core.result.Result
    (Array Std.U8 32#usize) r1_wire.Error) × Self)
  c2 : Self → (Slice aspis_core.field.QM31) → (Array aspis_core.field.QM31
    1024#usize) → Result ((core.result.Result (Array Std.U8 32#usize)
    r1_wire.Error) × Self)

/-- [aspis_r1_cost_probe::host_semantic::BuiltSemantics]
    Source: 'crates/aspis-r1-cost-probe/src/host_semantic.rs', lines 12:4-23:5
    Visibility: public -/
structure host_semantic.BuiltSemantics (H : Type) where
  bytes : alloc.vec.Vec Std.U8
  transcript : host_wire.SemanticTranscript H
  challenges : aspis_core.state_only_prefix.r0.Challenges
  alpha : Array aspis_core.field.QM31 10#usize
  state_before_z0 : Array Std.U8 32#usize
  roots : Array (Array Std.U8 32#usize) 2#usize
  columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize
  z : Array aspis_core.circle.SecureCirclePoint 2#usize

/-- [aspis_r1_cost_probe::transport::Variant]
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 3:0-3:30
    Visibility: public -/
inductive transport.Variant where
| S1 : transport.Variant
| S2 : transport.Variant
| D : transport.Variant

/-- [aspis_r1_cost_probe::prover::Backend]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 10:0-10:271
    Visibility: public -/
structure prover.Backend where
  hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)
  variant : transport.Variant
  domain : host_commitment.EncodingDomain
  messages : alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact
    1024#usize)
  c1 : Option host_commitment.Commitment
  c2 : Option host_commitment.Commitment
  c1_salts : Option host_commitment.PrivateSalts
  c2_salts : Option host_commitment.PrivateSalts

/-- [aspis_r1_cost_probe::prover::MaskedFixtureAudit]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 107:0-114:1
    Visibility: public -/
structure prover.MaskedFixtureAudit where
  c1_columns_inactive_balanced : Std.Usize
  mask_only_columns_inactive_balanced : Std.Usize
  d_inactive_balanced : Bool
  g_inactive_balanced : Bool
  h1_padding_inactive_balanced : Bool
  h1_total_balanced : Bool

/-- [aspis_r1_cost_probe::verifier::Error]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 20:0-27:38
    Visibility: public -/
inductive verifier.Error where
| Parse : verifier.Error
| Semantic : verifier.Error
| Transcript : verifier.Error
| Relation : verifier.Error
| Merkle : verifier.Error
| Query : verifier.Error
| Checkpoint : verifier.Error
| Allocation : verifier.Error
| Rejected : verifier.Error
| AttemptsExhausted : verifier.Error
| Entropy : verifier.Error

/-- [aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure#3]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 211:78-211:98 -/
@[reducible]
def prover.prove_masked_with_attempt.closure_3 (T0 : Type) := Unit

/-- [aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure#2]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 197:124-197:142 -/
@[reducible]
def prover.prove_masked_with_attempt.closure_2 (T0 : Type) := Unit

/-- [aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure#1]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 196:69-196:87 -/
@[reducible]
def prover.prove_masked_with_attempt.closure_1 (T0 : Type) := Unit

/-- [aspis_r1_cost_probe::prover::prove_masked_with_attempt::closure]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 195:92-195:110 -/
@[reducible]
def prover.prove_masked_with_attempt.closure (T0 : Type) := Unit

/-- [aspis_r1_cost_probe::prover::prove_masked_attempt::closure]
    Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 175:51-175:69 -/
@[reducible]
def prover.prove_masked_attempt.closure := Unit

def aspis_prover.state_only_hiding.StateOnlyMaskBuildError.read_discriminant
    (e : aspis_prover.state_only_hiding.StateOnlyMaskBuildError) : Isize :=
  match e with
  | .ZeroPrivateEntropy => 0#isize
  | .ReusedMaskNonce => 1#isize
  | .MaskSampleExhausted => 2#isize
  | .TraceShape => 3#isize
  | .Layout => 4#isize
instance _root_.ProverRwRngNativeBody.aspis_prover.state_only_hiding.StateOnlyMaskBuildError.instDiscriminant :
    Discriminant aspis_prover.state_only_hiding.StateOnlyMaskBuildError Isize where
  read_discriminant := aspis_prover.state_only_hiding.StateOnlyMaskBuildError.read_discriminant
end ProverRwRngNativeBody
