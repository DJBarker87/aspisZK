# D554 native zeroize bridge checkpoint

Branch `codex/pv-evh-20261029`, resume base
`e31a42c7b28d6dad534945af919511117f3a1386`. Same worktree and retained
runjoin32 cohort. Endpoint/deployment/privacy rows removed **NONE**.
**Target not yet established.** This is a context checkpoint, not budget
exhaustion, a host blocker, or a counterexample against shipped Rust.

## Established

* `DeployedZeroWorld` and `DeployedZeroSelected` replay the recorded V221/V222
  deployed zeroize 1.9.0 world/cursor/trace/byte/array laws. The checked replay
  changes imports and namespaces only. `zero-law-replay.json` and
  `zero-selected-replay.json` pin original/replayed bytes. RDCD's old cache is
  absent; its Result dictionary cohort conflicts with the retained cohort.
  No conflicting object was loaded, copied, substituted, or rebuilt. The laws
  were replayed as new PV_EVH modules in the SAME existing cohort instead.
* `ZeroAddressBridge.cells_deployed`, `cursor_history`, `cursor_overwrites`
  associate local owner-indexed byte recursion with deployed physical addresses,
  every volatile write and every per-element address-bearing assembly barrier.
  Project volatile_clear's single final fence is never substituted.
* `NativeZeroBoundary` proves op122/op123 remain residual at the actual
  opsNative selection, and exposes the exact emitted array/scalar dictionaries.
  `NativeZeroInstall.byte_dictionary`, `array_value_native`, `execution_native`
  compose the recorded source selection through
  `opsNative base heap box (PV_EVH_DeployedZeroSelected.selected ops)` and retain
  the post-memory world. Other residual fields are unchanged by that selection.
* `StackZero` separates stack slots from allocator-owned Runtime.State.heap.
  Deployed cleanup clears initialized bytes, preserves outside memory and the
  complete runtime frame, retains physical history and archives the retired
  slot without deleting its post-cleanup physical bytes.
* `StackCleanup` checks the original owner/identity and initialized64 extent;
  ordinary fill errors clean the full post-fill world, retaining partial writes
  and events. Abort retains the prefix and skips cleanup.
* `NativeStackDrop.native_drop64` joins actual native dictionary dispatch,
  zero source array, cleared physical memory, unchanged allocator/runtime state,
  retired slot, history and emitted events in one leaf theorem.
* `NativeEntropyError.error_native` joins the EXISTING extracted entropy
  `afterDraw` error branch at that native selection with partial-fill cleanup,
  complete source projection and retained events. `source_error` is a small
  symbolic Err branch, not recurrence normalization. This theorem retains a
  harmless unused ambient ExternalTypes parameter; all actual carriers and
  dictionary operations in its statement use the explicit native types base.

The inherited extraction's comments name zeroize1.8.1. Its dictionary routing
is used, **not its old effect law**: the deployed effects and source values are
supplied by the separately checked 1.9.0 law. `zero-native-binding.json` records
seven complete source-body associations and the exact native/source theorems.
This is structural source association under own-1 plus Lean laws; V370 remains
source-to-machine preservation. Native validation was reused, never rerun.

## Exact limits and before/after

Before: zeroize local sequences were not linked to the recorded deployed law
or native selector, and cleanup used an allocator-only heap representation.
After: the zeroize **leaf** source dispatch and physical/retired-memory laws
are connected, including the extracted entropy Err branch, under original
live-slot lookup/extent and the recorded residual source selection.

This does NOT establish the full native prover entry. Its residual dictionary
family is not yet provenance-fixed to that source selection. The entry must
establish original stack admission, exclusive initialized regions and complete
fill-driver restoration; heap/stack physical address coherence is not proved.
StackZero.Frame.runtime is retained, not silently identified with physical
memory. New NativeEntropyError.afterFill is the joined error control fragment,
not an installed replacement for the full EntropyStep/prover entry. Zeroize
success/inner32/later secret drops still require their actual source consumers.
The L3 register/spill/copy/retired-memory observer and joint law remain OPEN;
cleanup events are retained, never assumed silent or witness-independent.

Inherited ownership/allocation/capacity/diagnostic laws remain local at all
other frontiers. Actual System ValidAnswer, metadata/RawVec/Global association,
OwnedVec propagation through real consumers, all seven callback frames,
literal writer/syscall/io::Error destruction and installed hook/profile,
remaining primitives/options/hash/oracle bytes/mutable restoration and the
complete Q entry remain required. RuntimePublishInstall still uses the old
CapacityWorld constructor. D520/U/D524 client/account inputs stay explicit.

No trace-link or (v') completion credit: oraclePrefix/countTrace/nonce-store
fileTrace need full actual-family native adequacy first. NativeObstruction62
and op132 remain. No successful native run or nonemptiness witness is inferred.
T remains exactly entropy_law, entropy_kernel, observation; no trust item added.

## Attempts and checks

This resume used 14 charged attempts, IDs79500–79513: 9 accepted, 5 failed.
EVH10 total32:22 accepted/10 failed; **68 remain, NEXT79514**.
Both audit triplets79397–79399 and79597–79599 are untouched. No admission
refusal, pending compiler job, native/Kani execution, memory kill or cap change.
Every compile used one6G/8G/swap0/tasks64 scope and Lean-M7000, source committed
before staging. Standard axioms only on accepted results, all declarations
printed. Exact revisions/blobs/SHA/dependency/object hashes, exit, wall, peak
RSS and swaps remain in receipt-ID.json/out-ID.log/time-ID.log.

Failed sources are retained:79502 polymorphic field headers,79503 nested record
syntax/missing encoder namespace,79504 allocator lemma namespace,79505 nested
record syntax,79512 missing ExternalTypes carrier. Replacements changed proof
bytes:79506,79507,79513. No failed source was rerun unchanged. The79502 broad
field reduction took50.35s/4,616,200KiB; symbolic allocator field preservation
replaced it without a cap or heartbeat increase. No audit/manifest replay ran.

An optional unused-section-parameter cleanup after79513 was rejected by
stage.py's accepted-source immutability check BEFORE any host action. It was
restored byte-for-byte; no compiler attempt or new ID was consumed. All
accepted current sources remain exact receipt bytes. Do not "clean up" that
warning by changing an already accepted module.

Read-only audit.py also checks zero_law.py --check and zero_binding.py --check,
receipt/source/object coherence and native preflight. The native closure gate
must continue to FAIL on the retained frontiers. No endpoint rows, frozen
Rust/extraction/soundness files, other worktrees, keys/accounts/funds, or remote
branches were changed. No delegation or push occurred.
