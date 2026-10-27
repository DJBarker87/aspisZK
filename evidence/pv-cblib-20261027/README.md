# Library callback source campaign

Branch: codex/pv-cblib-20261027. Initial candidate revision:
`bd47052f039ae2d96060acb5607fe652ebe193d4` (unmerged prover candidate).
Target not yet established. Initial rows discharged: 0.

## Rules and budget

Read pv-common.txt including rulings (a)-(g), r1p-common.txt,
local-lean.txt, the root AGENTS.md and pv-host-restored.flag.
Host restored; no restoration polls required. Env-J IDs 39600–39899;
100 charged Lean attempts, with the final three reserved for bundle audits;
10 Kani runs. TALLY.json is the running ID/budget record. IDs are consumed
before admission and never reused. Native extraction receipts are separate
from these two budgets. No local Lean invocation is authorized.

The launcher currently uses TasksMax=64, despite the historical standing
exception permitting 128. No shared infrastructure is changed.

## Source and cache identity

See source-provenance.json and source/ for pinned third-party files.
The requested cb3 `lean-objects` cache is absent after the host deletion.
No binary copied from that absent path. Every Lean run records the effective
Env-J direct import objects and hashes. Imported ProverRw modules remain
read-only. Source-revision plus per-attempt source snapshots identify uncommitted
proof additions. Cargo library versions match the candidate Cargo.lock.

## First extraction outcomes

- op212 / V234: generic wrapper extraction passes Charon, but Aeneas rejects
  structured Drop. Direct broad path mistakenly selects DynDigest.finalize
  and is rejected for Drop and escaping references. Both are retained;
  neither is a source law for Digest's blanket implementation.
- A more precise impl pattern was rejected by Charon's start-from resolver;
  the documented form requires the impl as the first path element.
- op34 / V185: native Vec.is_empty extraction reaches Vec's hidden layout,
  unsupported by Aeneas. An owned safe P6 reference is required.
- charon-source-op212-004: admission before scope permitted; go barrier
  refused aggregate reservation (60,532,195,328 bytes > 55 GiB). No compiler
  ran, no Lean/Kani budget charged. Wait at least three minutes before retry.

No desired-output premises, new trust items, runtime effects, or source
changes are introduced by these diagnostic extractions. All rows remain OPEN.

## Focused Lean preflight

39600, 39602 and 39603 failed during development of the Bool/scalar zero
transport; their diagnostic `sorryAx` lines are rejected, never credited.
The changed proof at 39604 passes with `[propext, Classical.choice, Quot.sound]`.
39601 was a zero-charge scanner race on an unrelated vanished session cgroup;
retry used next ID after more than 30 seconds. No unchanged failed proof was
rerun. `PV_CBL_VectorShape.emptyReference_eq` proves a generic reference-model
identity, not a native source law or a discharged row.

The first exact-type Kani admission was refused at 02:25:53 UTC for aggregate
reservation (60,532,195,328 bytes already reserved); no Kani compiler ran.

## First published source selection

`PV_CBL_CallbackBundle.op34_source` compiles at 39610, after the changed
noncomputable selection at 39609. The executable compiler limit at 39607
(large ExternalFuns constructor) is retained and was not bypassed with a
runtime implementation override. All accepted axiom lines are standard.

P6 gate `kani-op34-exact-006` passes: 401 checks, no stubs, 19.19 s wall,
484,740 KiB process peak RSS, swap 0. It uses the actual private Word type in
host_commitment.rs: outer vector length 0..2, either Base/Secure payload
length 0..1, arbitrary u32 payload bits, every Error variant. This is bounded
native evidence, not a universal native allocator/world theorem. The Lean
source selection is unconditional at arbitrary logical Vec inputs and
payload types. The frozen native is_empty body and owned reference both test
`self.len() == 0`; retained source hashes identify that parametric body.

The live privacy endpoint is not rewired here. Candidate source-row supply
and native bounded evidence must not be reported as deployed RunJoin or
whole privacy closure.

## Three-operation stage: op34, op35, op32

Candidate source laws supplied: V185/op34 and V186/op35. Both have
unconditional full-Result Lean laws through PV_CBL_CallbackBundle at 39622.
`kani-op35-exact-002` passes 127 checks, including actual default Vec contents,
length and capacity for the prover's private Result<Word, Error> instantiation.
The Vec default source and reference both call Vec::new with no input payload.
No native unbounded allocator/CPU/world theorem is claimed.

V183/op32 is deferred to pv-runjoin for recoverable native allocation effects;
see NATIVE-EFFECTS.md. No desired-output premise replaces it.

Rejected follow-on fact attempts 39615/39616 are retained: a scalar-zero
transport, an unavailable Result.map API, and a redundant final tactic were
fixed in the source accepted at 39618. Failed diagnostics do not count as
accepted axioms. The preservation facts pass at 39619, inventory at 39620.

## Three-operation stage: op208, op25, op29

V177/op25 and V180/op29 now have source laws through the complete
PV_CBL_CallbackBundle.selectedAll carrier/dictionary (39650). Earlier stable
selected/op34_source/op35_source names are retained, with op34_source_all and
op35_source_all added for the full carrier. No source name was renamed.

PathBuf P6: kani-pathbuf-borrows-r01 passes all 353 checks: 1.23s wall,
175380KiB peak RSS, swap0. Native PathBuf bytes have arbitrary length0..4,
including invalid UTF-8; an arbitrary usize coordinate and lengths establish
both deref/as_ref byte observations against the actual owned PathBuf identity
reference. The native/owned input types are actual PathBuf. No layout stub or
filesystem effect is introduced. The source carrier keeps the existing
opaque PathBuf and interprets a Path view on that owned carrier.

The combined path_borrows gate timed out at180s and is preserved unchanged.
It combined Unicode String work and clone/full-slice observations. The
replacement removes that unrelated String contract and uses coordinate
observations without clone allocation. Caps/timeout/input-byte bound were
not raised. Its expired cgroup is gone and no attributable solver temp files
remain. GNU time's timeout RSS is explicitly incomplete, not a native peak.

V232/op208 remains OPEN: exact source body, carrier, full Result and selection
shape are compiled through39648, but compress256 is still an explicit missing
source binding (OP208-FRONTIER.md). No opaque compression parameter is counted
as row discharge.

## Prepared array/split stage

ArrayKernel/Image/Guard/Step/Unfold/Total/Prefix/Copied/Ext/ReferenceTotal and SplitBounds/Arithmetic/Model/Recompose were prepared after commit 6911addb1d. At this checkpoint they are **drafts, not accepted Lean proofs**; the first queue is awaiting host reservation (39656–39658 refused, zero charge). Op215 mono extraction and op36 borrowed full-Result extraction are rejected, with exact diagnostics in their native run directories. Neither is a new row law. See ARRAY-FRONTIER.md. Current accepted bundle remains four source callbacks.

Read-only LLBC validity audit: op215 monomorphized Charon process exited zero but its JSON has `has_errors=true` (type/trait errors in its log). It is rejected, not a successful extraction. Other existing LLBC files have `has_errors=false`; this flag alone does not certify source closure. The extraction runner now checks it before launching Aeneas. No frontend/backend or shared launcher repair was made.

## Pop and focused array continuation

Native run `pop-owned-first-r01` exited 1 because the selector omitted `host_commitment::`; it is charged with no equivalence verdict. The corrected selector run `pop-owned-qualified-r01` timed out at 180.31 s (exit 124), without verdict/counterexample. Its GNU-time wrapper RSS excludes killed descendants; no aggregate solver-RSS claim is made. The post-timeout check confirms its own cgroup is gone. A changed coordinate assertion harness is prepared under the same input bounds/caps/180-s timeout. Kani budget is 8/10.

Lean 39661 accepted the generic copy kernel. 39666 rejected the image helper because `prefix` was a reserved identifier; the source was corrected before retry. Lean budget is 38/100, with the final three still reserved for bundle audit. Current-source acceptance is tracked in proof-status.json; drafts are not certified by older green source snapshots.

Own queue timing now samples the standing read-only inventory after the required refusal wait, then invokes all unchanged positive admission and in-scope gates. It reserves nothing, modifies no host infrastructure, and consumes a fresh Env-J ID for each actual Lean admission attempt. Source/body errors are never automatically retried.

## Kani budget exhausted; Lean continues

`pop-coordinate-r01` and `path-join-string-coordinates-r02` both timed out at 180 seconds with no verification verdict and no checked counterexample. Their post-timeout checks confirm their own cgroups are gone. Together with earlier runs this exhausts **10/10 Kani**, and the runner forbids further charged Kani work. Wrapper GNU-time RSS after killed descendants is incomplete and is not presented as solver peak RSS. The array Kani harness and sha2/block-buffer vendor harnesses remain proposed, never run.

The owned direct-index array variant was rejected by Aeneas for reference-output loan validation and structured Drop/destructor semantics (`aeneas-source-op36-owned-opt-direct2-01`); it is not a source law. Manual LibraryShapes/LibraryShapeTypes/GenericArrayFlatten drafts describe byte-pinned Rust fields only; they are not Aeneas extraction or callback source-binding certificates. Additional source files are checked against Cargo.lock .crate archive checksums and matching archive member bytes in additional-library-sources.json.

No new callback row is supplied in this continuation. The canonical endpoint/ledger is unchanged; Native/RunJoin, deployment, E1/E2, L1/L2/L3 and client-route conditions remain retained. The source/reference/toolchain association caveats remain explicit.
