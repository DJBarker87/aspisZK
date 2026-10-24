# Bounded immutable export request to the lead

Dependent action stopped before any Lean invocation. Please release an immutable,
read-only **untrusted declaration transport** for the following existing objects
and selected closure, produced by the owning source session. This is a request
for missing data; no new source change, host build, trust grant or broad replay
is requested. Do not send only source equality or an axioms/type listing.

## Current source side

Revision: `9acc015544c36891712af984c0a9604a39425eeb`.
Directory: `docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021/`.
Targets and primary seeds:

- S6SdkDependencyFactorV1: every declaration emitted from all fourteen selected
  spans, including the complete Account/Record/Entry/Heap/Library/Allocator/
  AeneasExtraction/runtime structures, both wrappers and generated auxiliaries.
- S6SdkStage1ReuseFactoredV1:
  `AspisS6SdkStage1ReuseFactored.public_read` and `accepted_sdk_stage1`.
- S1SdkStage1AccountNumericV1:
  `AspisS1ValuesOwnedInstallation.sdk_stage1_account_numeric`.

Additional current seeds for concrete consumed-instance comparison:
`AspisS6CurrentStage1FirstFields.accepted_stage1`,
`AspisS1ValuesOwnedInstallation.owned_stage1_account_numeric`,
`AspisS6CurrentFirstInstallation.{install,current,first_decoded_eq}`,
`AspisS1ValuesOwnedInstallation.{withValues,nativeValues,expandValues}`,
`AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers.install`,
`AspisS1ExtractedRoundChildren.children`, and the exact existing decoder,
FirstComposition firstCurrent and preparation terms occurring in the two full
statement artifacts. Follow their dependencies; do not replace terms with
renamed wrappers. Include full theorem bodies, not just proposition statements.

`Port27SDK_export-request.json` pins the published source and original object
hashes. Object hashes are metadata copied from immutable receipts; this worker
has NOT opened those objects. An exporter must verify them against the owner
objects and retain .server/.private parts where relevant. Dirty overlays and
external source provenance must be stated explicitly, never attributed to Git.

## Original historical source and enclosing caller side

Factor source origin: full revision recorded in `Port27SDK_export-request.json`
(resolution of 97caa13d92). Export the same-name original declarations from all
fourteen original modules listed in the audit, plus the complete dependency
closure of `AspisR1.S2W_D189Consolidation.accepted_run` and `wrapper_frames`.
Include `S2W_NativeConsolidation.{FirstCut,SecondCut,SourceCuts,cuts_of_acceptance}`,
`S2W_ScheduledConsolidation.accepted_run`, the expanded child/mark definitions,
and `S2W_DigestExtraction.{AeneasExtraction,sourceBoundary,native_binding}`.
Those are the existing approved conditional producer and its actual lower
constructors; retain every condition. Exact source-only statement is attached.

The released Port18 canonical manifest has 15,241 declarations, but NONE of the
three current SDK primary seeds and NONE of the three current target module
transports. Its source bases are root5544611e5f/Aa4fa5c5, not current A9acc015544.
Do not relabel that transport. If the enclosing Port18 driver is part of the
intended join, its existing released canonical transport can be supplied under
its original manifest and reused only after complete sameDeclaration checks.

## Transport and acceptance contract

Use the Port18 raw saveModuleData pattern: per original module, constants and
constNames only; empty imports/extraConstNames/extension entries; no initializer
or trusted original import. Preserve every Expr, name, binder, level parameter,
proof/opaque value and metadata byte logically unchanged. Retain complete
constructor/recursor/mutual groups, rule RHS dependencies, and private names.
No private-name/binder rewriting, source-normalization equivalence or truncation.

Emit a full transitive constant dependency closure from types AND values with
`allowOpaque := true`, inductive mutual/constructor groups, recursor groups and
rule RHS. Iterate until unresolved is EMPTY (or explain each standard sysroot
leaf with exact hash). Provide duplicate-name conflicts from BOTH sides in full;
no first-wins conflict acceptance. Nonidentical complete declarations stop
selection pending a concrete analysis. Keep original object/source/transport
origins separate. Include edges and source/object/module part hashes and sizes,
exact exporter source/toolchain/sysroot hashes and full source assessments.
Transport and any derived JSON above 5 MB stay outside Git, represented in this
packet by SHA256+size+retained location and a complete manifest. Include proof
receipt commands, revisions, exits, wall/RSS/swap and full #print axioms for the
exported current theorems as historical evidence, not a fresh identity gate.

Once released, this worker can hash/pin into its own retained path, reuse the
maintained Port18 checking safeguards, reconstruct smallest dependency stage
first, then the concrete consumer, then one focused normal-import/full axioms
and declaration audit within six slots if the closure fits. The environment
must reject project axioms/unsafe/partial terms and mismatched preexisting
constants, kernel-check via addDeclCore at defaults, regenerate constructors/
recursors and compare ALL chosen complete ConstantInfo afterward. Reuse the
seven existing rejection tests explicitly as historical validation.
