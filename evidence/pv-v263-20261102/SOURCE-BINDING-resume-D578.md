# Resume D578 context checkpoint — target not yet established

Same sparse worktree and `codex/pv-runjoin-20261026`, entry `6ee81e0f24`.
No push or merge. This is an incomplete context checkpoint, not completion,
budget exhaustion or an impossibility claim. All three requested targets remain
OPEN: complete deployed host_work.map association, actual opsNative installation,
and actual reached successful execution/Nonempty P. No endpoint premise removed.

## Exact accepted increment

Seven new modules; all earlier accepted modules remain byte-identical:

* `PV_V263_RawGrowth` (79964): exact grow_one minimum/doubling/required-capacity
  planning, allocate versus grow request with retained old pointer/bytes/align;
  no allocator call on a reserved push; complete allocator-fault prefix.
* `PV_V263_GrowingPush` (79966): a stateful owned push. Allocator answers precede
  pointer/capacity commit and value store. Reserved branch returns directly,
  without an arbitrary failing method hook. Reservations may be strengthened to
  known physical capacity; old allocation is retained until resize success.
* `PV_V263_GrowingFacts` (79968): exact successful and faulted growing-push
  results, including post-world/events, stored values and retained layout.
* `PV_V263_GrowthSchedule` (79969): fifteen non-ZST handle pushes request
  capacities 4,8,16 for element sizes 2..1024; size1 gives 8,16; large elements
  give 1,2,4,8,16. This is a successful-path request plan, not syscall timing.
* `PV_V263_OwnedForks` (79970): delayed retained-family tasks are stored through
  GrowingPush, with a real owned handle-Vec descriptor. Spawn faults occur
  before push, callbacks or remaining spawns and preserve exact prefix/state.
  Vec::new uses the alignment-based dangling pointer and raw capacity zero.
* `PV_V263_OwnedIterator` (79973): original allocation and moving cursor are
  distinct. next transfers one value without an allocator/lifecycle request;
  non-ZST pointer advances by element size, ZST cursor stays aligned and its end
  encoding wraps by usize modulus. Exhaustion keeps the original release
  descriptor. Exhausted drop preserves the exact deallocator world/events,
  with a destructor panic converted to abort. Abort does not invent unwind
  cleanup. Native typed reads/provenance are not proved by this record.
* `PV_V263_LayoutBounds` (79974): unchecked RawVec doubling cannot overflow for
  a valid sized allocation. Layout::repeat's true bound is
  isize::MAX+1-align. For type-aligned strides and an alignment dividing
  isize::MAX+1, array_limit proves equivalence to the RawGrowth byte bound.
  Actual type-layout/bit-rounding association remains explicit.

These are local source-operation models/laws, NOT a complete native binding.
OwnedForks and OwnedIterator are not installed into the whole RetainedSpine:
that spine still uses abstract vector/lifecycle hooks and list-based joins.
Neither Owner nor Iter is a native byte-heap/provenance witness. Commit titles
referring to binding a loop mean this local source-shaped loop only.

## Mechanical source and native evidence

`growth-source-binding.py` checks thirteen COMPLETE pinned Rust 1.94.1
RawVec/Layout bodies and the five accepted model-source hashes. It retains
all source overflow paths and names the validity/alignment/byte-heap gaps.
`iterator-source-binding.py` checks nine COMPLETE iterator/handle definitions
and two accepted model-source hashes. These are local STRUCTURAL arguments,
not extraction identity, machine proofs or complete worker association.
Reports: `growth-source-binding-continuation.json` and
`iterator-source-binding-continuation.json`. Newly fetched rust-src files are
committed with `handle-std-source-pins.json`; fetch was read-only, no compiler.

The handle's returned T is behind Arc<Packet<T>>; Packet itself contains the
result. Thread uses Pin<Arc<Inner,System>>, separately from the Global handle
Vec. Thus the capacity census is not a census of thread/packet allocations.
The Unix pthread_t/Arc/Pin/Global/System layout laws remain under the native
layout/compiler boundary; no arbitrary monomorphisation machine proof claimed.

N90125 is optimized rustc1.94.1, release-style checks off, panic=abort, cfg
r1p-check+ct-host-prover, one6G/8G/no-swap/tasks64 scope. It executes fifteen
actual scoped-handle pushes for EACH of three representative payload types,
including a field-result shape and a large payload. All measured handles are
24bytes/alignment8 and capacities4,8,16. Non-growing pushes keep their pointer.
A changed-minimum-capacity policy FAILS with SIGABRT as intended. Original
stdout/stderr, commands, results, input hashes and timings are retained.
This is SAME-INPUT FINITE std validation, not actual encoder/SemanticOracle
callback execution, full-crate feature parity, deployed capture success or
proof of the whole source. Old N90122 exhaustion evidence is not rerun.

## Remaining requested targets, in dependency order

1. Interpret owned allocations/moves/iterator cursors in the native byte heap,
   with validity, type layouts and disjointness. Integrate precise growth,
   reserved methods and original-buffer iterator drops into the COMPLETE
   deployed worker spine. Bind closure/Arc/Packet/handle/scope/TLS lifecycles,
   native deferred schedule and EVH request/answer/event codec. Source structs
   and token identity do not discharge these. Account for System allocations,
   stack/environment/diagnostics and actual callback resource requests.
2. Install the SOURCE-BOUND operation at ACTUAL opsNative and reify/thread its
   state through ACTUAL capture. NativeBoundary.retained is unchanged: op257
   remains residual; Sequential64.worker reuses w. Source Result(Vec T) has no
   native fault/post-world channel. Use a stateful native reification and partial
   source projection, never fallback source answers or fabricated fail/div.
3. Discharge exact C1/C2 encoders and SemanticOracle/evaluate_assignment at the
   actual captured inputs, then construct the actual resource-granting run and
   Nonempty P. Existing grants, capture equations, schedule arithmetic and
   op227 equality do NOT supply those laws. No constant oracle, zero claims,
   arbitrary successful vectors or callback-totality endpoint premise added.

V400-257-entry/layout/lowering/callback/answer-timing, V370 and D381/D386 remain
P obligations. Existing V183 SUSPENDED(K-3) stays suspended. Three TrustItems,
seven links, observer, simulator, frozen Rust and release pins are unchanged.
Before/after V263 OPEN→OPEN, op257 residual→residual, Nonempty P unproved→unproved.
Zero rows or endpoint premises added, removed or changed. Skeleton consistency:
reduced to non-emptiness. No key/fund, Kani, SBF or ELF operation.

## Validation and remaining allocations

Continuation12 charged Lean attempts:7 accepted/5 rejected, IDs79963–79974.
Rejected79963/65/67/71/72 have committed original source revisions and complete
original logs; changed sources replace them. No unchanged failed source rerun.
New Lean wall34.71s,peak4,525,649,920bytes,swap0. Cumulative75/97 original-block
attempts:42 accepted/33 rejected,wall184.83s,peak4,561,240,064bytes,swap0.
Next79975;22 original normal attempts remain;79997–79999 audits UNUSED.
ADDITIONAL authorized91300–91396 normal block:97 UNUSED;91397–91399 audits
UNUSED. Total normal119 remain. Own wrapper still admits only799xx and the
original97-attempt block: before the first913xx launch extend ONLY the accepted
ID/budget checks, record the diff, and scan cross-job receipts/sent table.
Native6/20 charged,14 remain,nextN90126;0Kani. N90125 wall1.36s,
peak136,654,848bytes,swap0; compile/run exit0,matched control exit-6 expected.

All launches have before-launch ID scans and allowed:true+exit0 admission in
one shell; one scope at a time,Lean-M7000,normal heartbeat/recursion limits.
No new refusals, cap increase, memory kill or full/frozen manifest replay.
All accepted #print axioms are SUMMARY-BASED, standard only. No raw/NEP,
coherence or release audit is claimed. Failed-source guard unchanged.
Final preflight4307 project objects/9659 dependency fingerprints/5673 external
objects/5438 IR companions all match;9980 namespace resolutions match with
zero links/copies. Seven-source discipline scan and accepted-source/object/
no-live-own-scope reconciliation pass. All evidence inputs tracked, no file>20MB.
Exact per-target receipts/logs and source revisions remain authoritative.
