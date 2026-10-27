# First-half library model fidelity audit

Audit verdicts: 3 FAITHFUL (two relative to P7), 4 UNFAITHFUL (two retained power helpers), 85 UNDETERMINED. No premise removed. Headline remains
`AspisR1.RPx_Deployed.deployed`; frozen3 and narrowed D188 retained.

Assignment: first 92 of 184 rows whose inventory counterpart is exactly
`library model`, sorted by declaration name (stable ties). Last assigned:
`core.iter.traits.iterator.Iterator.all.default`; the second half begins
`core.iter.traits.iterator.Iterator.any.default`. Full hashes and row identities:
`KSC1_assignment.json`. Several inventory-labelled rows are Aspis carriers,
helpers or shipped-function stand-ins; a library label cannot supply fidelity.

The KSA dependency witnesses and raw-body occurrence counts are retained as
static prioritisation data, not dynamic call frequencies or reached-path proofs.
Neither inventory proves actual execution frequency on the adopted path.

Limits: 80 Lean attempts, 10 Rust runs, zero Kani; one admitted scope at a time.
All existing source, candidate and host objects remain read-only. Only KSC1_
modules and this evidence directory are changed. No shipped-file change; no
ELF rebuild triggered. No key action.

## Stage 2: checked observations

KSC1_L002 proves the mixed front/back singleton counterexample in the unchanged
KSA name-isolated kit. KSC1_R002 executes the corresponding real std calls on
Rust 1.94.1 (e408947bf): native yields `None`, kit yields `Some 7`.
The native suite also exercises mutation restoration, array borrowed iteration,
stateful from_fn/map, panic prefixes/partial-initialisation drop, equality,
empty, reverse-fold and all/collect short-circuit paths.
KSC1_R001 stopped before compilation because Cargo could not locate rustc;
R002 explicitly pins RUSTC to the installed 1.94.1 binary. No launcher changed.
The initial failed setup is retained and receives no validation credit.

KSC1_L004 proves exact equality to the resolved P7 slice equality operation,
and proves the full-length condition required for `Array.from_slice` restoration.
It also makes explicit that `XRn_Join_next` is only a projection of the P7
operation: it discards the element-restoration continuation. That identity is
not a proof of general mutable iteration fidelity.
KSC1_L006 proves indexed callback-state traversal and fromFnState agreement
with that traversal for arbitrary callbacks, including Result failure/divergence.
Its proof is a names/import-only reuse of XRp_FromFnState, not a new source
association. The original module is read-only. KSC1_L009 proves the monadic
De Morgan law, hence exact P7 slice inequality, preserving short-circuit failures.

No native fixture or traversal theorem proves arbitrary mutable-reference
aliasing, panic heap effects, drop effects or adopted-path reachability.

## P7, Rust semantics and native coverage

The exact selected Aeneas `.olean` paths and SHA-256 hashes are pinned in every
Lean configuration/receipt under `deps_fingerprint.aeneas_library_objects`;
imports and their split object companions are pinned by the unchanged runner.
The base is the coherent SInt2 objects, preceded only by read-only private KSA
kit objects and this job's KSC1 objects. `KSC1_kit_pins.json` verifies current
kit and isolated-copy bytes against the retained name-only isolation receipt.
No kit source/body was repaired or swapped during testing.
`KSC1_P7_sources.json` records reference source hashes; **the kernel-printed
resolved definitions in L004**, rather than source-file resemblance, establish
which definitions the equality proofs actually use. L012 queries the imported
kernel environment: none of the assigned std external names is already supplied
at its exact `Aeneas.Std` name; slice equality/inequality, mutable `next`, array
conversions and generic `collect.default` are present as the cited substrate.

The pinned documentation is Rust **1.94.1**, not the current unversioned docs.
`KSC1_rustdocs.json` pins the downloaded rust-lang/rust tag's rustdoc-bearing
source files and SHA-256 values. The web reader failed on the versioned pages;
direct HTTP retrieval succeeded. Documentation sources:

- [`from_fn`](https://doc.rust-lang.org/1.94.1/std/array/fn.from_fn.html),
  [tagged source](https://github.com/rust-lang/rust/blob/1.94.1/library/core/src/array/mod.rs#L55):
  exactly N ascending indices, no callback for N=0, mutable closure state
  threads between calls. [`array::map`](https://doc.rust-lang.org/1.94.1/std/primitive.array.html#method.map)
  consumes the array and calls FnMut on each element. Model `fromFnList` and
  `mapListFnMut` are traversal helpers, not standalone std APIs. L006 establishes
  the explicit indexed traversal identity; it does not prove non-Copy ownership,
  externally borrowed capture write-back, destructor effects or panic heaps.
  R003 tests ascending state/final state, empty calls, panic at first/interior/last
  indices, cleanup of two initialized from_fn elements and all three consumed
  array-map elements. Panic is represented by model `fail .panic`, but a heap/drop
  simulation is still missing. Result `.div` is propagated by the symbolic proof;
  no finite native run can validate divergence.
- [`DoubleEndedIterator`](https://doc.rust-lang.org/1.94.1/std/iter/trait.DoubleEndedIterator.html),
  [tagged source](https://github.com/rust-lang/rust/blob/1.94.1/library/core/src/iter/traits/double_ended.rs#L4):
  front and back share a range and cannot cross. The singleton counterexample
  violates this value law without needing mutation or a panic. Native R003 also
  checks empty and lengths 1–4, front/back/rev writes, enumerate writes and
  chunks_exact_mut writes (including untouched remainder). The last is a substrate
  probe, **not** a verdict about the other worker's chunks model.
- [`Iterator`](https://doc.rust-lang.org/1.94.1/std/iter/trait.Iterator.html),
  [tagged source](https://github.com/rust-lang/rust/blob/1.94.1/library/core/src/iter/traits/iterator.rs):
  map is lazy, collect delegates to FromIterator, reverse fold takes back elements,
  and all returns true on empty input and stops at the first false result,
  leaving the following iterator suffix available. Callbacks may panic;
  calls after the panic are absent. R003 tests empty/nonempty collection, mapped
  order, reverse fold order/empty/panic, all empty/continuation/short-circuit/
  remaining suffix/panic. General FnMut/external-borrow state and FromIterator
  effects remain open even though these control-flow fixtures pass.
- [`array/slice equality`](https://doc.rust-lang.org/1.94.1/std/primitive.array.html#impl-PartialEq%3C%5BU;+N%5D%3E-for-%5BT%5D),
  [tagged source](https://github.com/rust-lang/rust/blob/1.94.1/library/core/src/array/equality.rs#L43):
  differing lengths yield false for eq and true for ne; matching lengths use the
  element comparison. The kernel proofs are equality to P7's actual definitions,
  including their comparator `ne` calls and monadic short-circuiting. They retain
  P7's comparator/ABI interpretation; they do not independently certify arbitrary
  Rust trait implementations. R003 covers empty/equal/length mismatch/value mismatch.
- [`Vec::is_empty`](https://doc.rust-lang.org/1.94.1/std/vec/struct.Vec.html#method.is_empty),
  [tagged source](https://github.com/rust-lang/rust/blob/1.94.1/library/alloc/src/vec/mod.rs#L2957):
  the shared query is exactly len==0, with no callback, allocation, mutation or
  panic branch. L011 proves that law for the kit's arbitrary vector/type/allocator;
  R003 checks both outcomes. No mutable borrow is taken here.
- Mutable array IntoIterator and slice/array conversion use the same elements,
  with writes through yielded mutable references visible after the borrow ends.
  [Array IntoIterator docs](https://doc.rust-lang.org/1.94.1/std/primitive.array.html#impl-IntoIterator-for-%26mut+%5BT;+N%5D)
  and [slice iteration docs](https://doc.rust-lang.org/1.94.1/std/primitive.slice.html#method.iter_mut)
  describe that interface. P7 `Array.from_slice`'s mismatched-length fallback is
  explicitly labelled unreachable in its source; L004 exports the exact length
  hypothesis. R003 tests concrete post-borrow write-back, but the unrestricted
  adapter law requires a proof that the whole restoration chain meets that
  hypothesis. A shortened `IterMut` payload is not by itself that full slice.

The proposed minimal repair for mutable next_back is to call the shared
next_back model on **`⟨s.slice, s.i⟩`**, instead of **`⟨s.slice, 0#usize⟩`**,
retain `s.i` in its result and retain the element restoration continuation.
This repairs the exhibited front/back selection defect; it is **proposed only**,
not installed or proved universally faithful. Prove valid restoration length,
ordered mutation write-back and callback/borrow transport before crediting
consumers. `reverseNext` and `nextBackPair` must consume the corrected operation.
No claim that the counterexample is reached in a frozen verifier execution.

The Windows, chunks_exact_mut model, IterMut direct next_back/all/fold models
and the other half's iterator externals are outside this assignment. The shared
next_back defect is identified only as the dependency of our two refuted wrappers.
Neither native substrate coverage nor constructor roundtrip closes those rows.

## Stage 2 completion

L010 proves the reverse wrapper counterexample and the separate singleton
changed-element restoration/empty observations. L011 proves Vec.is_empty's
complete shared-query law. L014 proves finite stateful from_fn/fromFnState and
map fixtures matching R003, using the symbolic `add_value` theorem rather than
reducing platform-dependent usize additions. These finite fixtures do not remove
the general callback/borrow/drop obstructions in the table.

R003 adds array-map panic/drop, reversed-fold panic, first/last from_fn panic
and empty borrowed-iteration/equality cases. Its private scratch root copies the
frozen Cargo.toml and Cargo.lock and reads the frozen source tree through symlinks;
no second corpus copy or other worker edit is made. The diagnostic is std-only,
compiled directly with pinned rustc `-O -C overflow-checks=yes --test`, inside
the capped Rust scope. This is an explicitly optimized scratch cfg(test) profile,
not a deployed-ELF profile claim. Cargo metadata runs locked/offline first.
R003 additionally hashes every frozen manifest and validates resolved dependency
edges against the frozen lock. R002 has the prior package-membership graph
validation; R001 never reached graph validation and receives no test credit.
The lock is unchanged in R002/R003. Exact graph and edge receipts are committed.

Only the existing S2H reservation and unchanged S2W host runners are used. No
launcher, monitoring or admission infrastructure was changed. Failed elaboration
attempts are retained, including their diagnostic sorryAx prints; none is accepted.
No timeout or memory kill occurred, and no caps were raised.
