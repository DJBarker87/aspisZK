# First-half library model fidelity audit

Audit verdicts: 3 FAITHFUL (two relative to P7), 4 UNFAITHFUL (two retained power helpers), 88 UNDETERMINED. No premise removed. Headline remains
`AspisR1.RPx_Deployed.deployed`; frozen3 and narrowed D188 retained.

Assignment (corrected final filter): first 95 of 189 rows whose counterpart
begins with `library model`, sorted by declaration name (stable ties), with the
odd half rounded up. Last assigned:
`core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect`;
the second half begins `core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold`. Full hashes and row identities:
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


## Scope correction retained

The initial stage used equality with the label `library model` (184 rows) and
covered its first92. Final review identified five additional inventory rows
labelled `library model (derived Clone/PartialEq, ...)`; excluding that suffix
was too narrow. The final assignment is first95 of all189, half rounded up.
All five added derive rows are UNDETERMINED: their actual nominal-source-carrier
and derive-operation associations and native derive differentials are absent.
The previous Rev.fold and Iterator.all observations are supplementary only, in
KSC1_supplementary.json; no second-half row is claimed as assigned or closed.
The table/JSON retain exact names and split boundary so the lead can reconcile
any different odd-row convention without treating a row as silently completed.


## Per-model verdicts (complete corrected assigned half)

Ordering uses retained KSA kernel witness counts, then qualified raw-emission
occurrences, as the available static use evidence. These are first-unresolved-node
witnesses, **not exhaustive kernel fan-in or measured reached-path frequency**.
No adopted-run frequency certificate exists in this packet; that exact ordering
requirement is UNDETERMINED. Alphabetical assignment numbers preserve the split.
The raw short-name substring counts in the assignment are not usage evidence.

FAITHFUL for equality/inequality means exact equality to the **resolved P7 base**;
P7 trust, comparator/ABI admission and caller reference validity remain. The
Vec verdict is against the documented shared-query operation. All other scoped
positive lemmas are recorded without upgrading the full operation's verdict.
The two retained power failures are not new library defects. Full source hashes,
kernel names, locations, static counts and obstructions are in KSC1_verdicts.json.

| Assignment row | Declaration (qualified where inventory supplied it) | Use witnesses | Kind | Verdict | Evidence / exact obstruction |
|---|---|---:|---|---|---|

| 92 | `core.array.fromFnList` (XRn_Join_FunsExternal.lean:72) | 14 | from_fn traversal helper | **UNDETERMINED** | No P7 definition at this name. L006 indexed_eq proves all loop iterations/state/error propagation against an indexed traversal. Fuel/index helper accepts states not reachable from N/0; no complete Rust mutable capture, drop or panic-effect relation. R002 covers empty/success/panic. |
| 29 | `XRn_Join_asSlice` (XRn_Join_CheckpointModel.lean:6) | 13 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_asSlice is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 71 | `XRn_Join_word` (XRn_Join_ByteFields.lean:6) | 10 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_word is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 37 | `XRn_Join_intoIter` (XRn_Join_ABI.lean:25) | 8 | array mutable IntoIterator ABI | **UNDETERMINED** | P7 Array.from_slice silently returns original array when restored length differs. L004 proves writeback only at full length. Must prove every legal restore chain supplies that full slice and all mutations; no unrestricted law follows from native R002. |
| 5 | `XRo_Join_Carriers.C.E` (XRo_Join_Carriers.lean:8) | 7 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.E is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 34 | `XRn_Join_enumerateNext` (XRn_Join_ABI.lean:5) | 7 | enumerate next ABI | **UNDETERMINED** | P7 next supplies element writeback; wrapper preserves supplied item via Prod.snd. Missing valid mutable-reference carrier/continuation proof and reached usize counter bound (checked overflow differs from wrapping profiles); ignores supplied Iterator dictionary. R002 covers basic enumeration only. |
| 70 | `XRn_Join_usize` (XRn_Join_DotModel.lean:33) | 7 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_usize is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 65 | `XRn_Join_scanWord` (XRn_Join_QueryModel.lean:7) | 5 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_scanWord is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 94 | `core.array.mapListFnMut` (XRn_Join_FunsExternal.lean:98) | 5 | array::map traversal helper | **UNDETERMINED** | No P7 same-name definition. Output subtype proves length and recursion threads F; no relation to Rust ownership of non-Copy input/output, partial mapped Drop, or external capture restoration. R002 success-order fixture only for this helper. |
| 93 | `core.array.from_fn` (XRn_Join_FunsExternal.lean:87) | 4 | array::from_fn | **UNDETERMINED** | No P7 same-name definition. Traversal threads F internally but drops final F from API; arbitrary external mutable-capture restoration and panic drop are unassociated. R002 final external state16/drops2 alone cannot prove this missing relation. |
| 74 | `XRo_Join_Installed.actual` (XRo_Join_Installed.lean:16) | 4 | Aspis dictionary/helper (mislabelled library) | **UNDETERMINED** | XRo_Join_Installed.actual assembles a dictionary/selects a result or defines a test Copy instance. Missing emitted/adopted dictionary association, not a Rust std fidelity obligation. Do not infer closure from projection/slot equalities. |
| 85 | `XRn_Join_FieldExternal.canon` (XRn_Join_FieldExternal.lean:17) | 4 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_FieldExternal.canon is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 35 | `XRn_Join_enumerateRestored` (XRn_Join_ABI.lean:44) | 3 | enumerate borrow ABI | **UNDETERMINED** | Constructor returns iter/count0 and projects iter on restoration. Missing arbitrary legal continuation/element-writeback law and reachability of the dictionary/borrow carrier; native R002 is a fixture. |
| 1 | `XRo_Join_Carriers.C.Challenges` (XRo_Join_Carriers.lean:11) | 2 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.Challenges is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 15 | `XRo_Join_Carriers.E.Q` (XRo_Join_Carriers.lean:21) | 2 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.Q is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 62 | `XRn_Join_revRestored` (XRn_Join_ABI.lean:37) | 2 | rev borrow ABI | **UNDETERMINED** | Constructor/projection lens alone is not arbitrary continuation fidelity; consumer uses refuted next_back. Prove corrected next_back, legal borrow restoration and fixed dictionary association before use. R002 covers basic reversed writes. |
| 87 | `XRo_Join_Carriers.cd` (XRo_Join_Carriers.lean:66) | 2 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.cd converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 95 | `core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect` (XRn_Join_StdExtra.lean:60) | 1 | Map::collect | **UNDETERMINED** | P7 collect.default supplies delegation but local Map.next loop has no proved arbitrary FromIterator/callback effect/ref-ownership law. R002 empty/success/panic prefix only. No whole collection or heap-effect proof. |
| 7 | `XRo_Join_Carriers.C.Err` (XRo_Join_Carriers.lean:18) | 1 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.Err is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 13 | `XRo_Join_Carriers.E.Prepared` (XRo_Join_Carriers.lean:29) | 1 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.Prepared is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 14 | `XRo_Join_Carriers.C.Q` (XRo_Join_Carriers.lean:7) | 1 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.Q is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 17 | `XRo_Join_Carriers.E.ST` (XRo_Join_Carriers.lean:26) | 1 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.ST is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 25 | `XRo_Join_Carriers.E.V` (XRo_Join_Carriers.lean:22) | 1 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.V is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 26 | `XRo_Join_Carriers.C.View` (XRo_Join_Carriers.lean:15) | 1 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.View is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 31 | `XRn_Join_digest` (XRn_Join_CheckpointModel.lean:8) | 1 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_digest is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 72 | `XRn_Join_wordBytes` (XRn_Join_ByteFields.lean:26) | 1 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_wordBytes is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 76 | `XRo_Join_Carriers.arr` (XRo_Join_Carriers.lean:34) | 1 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.arr converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 82 | `aspis_core.r0.domain.FibreIndex` (XRn_Join_TypesExternal.lean:18) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | aspis_core.r0.domain.FibreIndex is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 9 | `MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter` (XRn_Join_FunsExternal.lean:119) | 0 | array borrowed IntoIterator | **UNDETERMINED** | P7 to_slice/from_slice substrate only. Whole continuation must restore a full-length slice and all yielded mutable items; no arbitrary-context invariant proved. KSC1.P7.restored_array; R002 writeback probe. |
| 80 | `aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne` (XRn_Join_FieldExternal.lean:40) | 0 | derived Aspis Clone/PartialEq external | **UNDETERMINED** | aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne: scalar identity/structural comparison looks plausible, but no pinned P7 declaration for this Aspis derive and no proved relation between the source newtype/record and kit carrier. Actual derive expansion, nested limb comparison including noncanonical representatives, panic/error freedom and unchanged borrow ownership require association. No fresh native derive differential; std u8 equality fixtures do not cover this model. |
| 20 | `Slice.Insts.CoreCmpPartialEqArray.eq` (XRn_Join_FunsExternal.lean:179) | 0 | slice/array PartialEq | **FAITHFUL** | KSC1.P7.slice_array_eq (L004): exact equality to pinned P7 core.slice.cmp.PartialEqSlice.eq, with arbitrary comparator, lengths and Result branches. P7 trust retained; not independent Rust comparator refinement. |
| 21 | `Slice.Insts.CoreCmpPartialEqArray.ne` (XRn_Join_FunsExternal.lean:186) | 0 | slice/array PartialEq | **FAITHFUL** | KSC1.P7.slice_array_ne_p7 (L009): exact equality to pinned P7 ne, monadic De Morgan proof preserves errors/divergence and short-circuit. P7 trust retained. |
| 75 | `alloc.vec.Vec.is_empty` (XRn_Join_FunsExternal.lean:174) | 0 | Vec::is_empty | **FAITHFUL** | KSC1.vec_is_empty (L011) proves ok(length=0) for arbitrary element type/allocator/vector. Shared query, no allocation/callback/writeback or panic branch. Rust1.94.1 vec/mod.rs:2957-2959; native R002 tests zero/nonzero. |
| 77 | `aspis_core.field.M31.Insts.CoreCloneClone.clone` (XRn_Join_FieldExternal.lean:31) | 0 | derived Aspis Clone/PartialEq external | **UNDETERMINED** | aspis_core.field.M31.Insts.CoreCloneClone.clone: scalar identity/structural comparison looks plausible, but no pinned P7 declaration for this Aspis derive and no proved relation between the source newtype/record and kit carrier. Actual derive expansion, nested limb comparison including noncanonical representatives, panic/error freedom and unchanged borrow ownership require association. No fresh native derive differential; std u8 equality fixtures do not cover this model. |
| 78 | `aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq` (XRn_Join_FieldExternal.lean:32) | 0 | derived Aspis Clone/PartialEq external | **UNDETERMINED** | aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq: scalar identity/structural comparison looks plausible, but no pinned P7 declaration for this Aspis derive and no proved relation between the source newtype/record and kit carrier. Actual derive expansion, nested limb comparison including noncanonical representatives, panic/error freedom and unchanged borrow ownership require association. No fresh native derive differential; std u8 equality fixtures do not cover this model. |
| 79 | `aspis_core.field.QM31.Insts.CoreCloneClone.clone` (XRn_Join_FieldExternal.lean:39) | 0 | derived Aspis Clone/PartialEq external | **UNDETERMINED** | aspis_core.field.QM31.Insts.CoreCloneClone.clone: scalar identity/structural comparison looks plausible, but no pinned P7 declaration for this Aspis derive and no proved relation between the source newtype/record and kit carrier. Actual derive expansion, nested limb comparison including noncanonical representatives, panic/error freedom and unchanged borrow ownership require association. No fresh native derive differential; std u8 equality fixtures do not cover this model. |
| 81 | `aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.ne` (XRn_Join_FieldExternal.lean:56) | 0 | derived Aspis Clone/PartialEq external | **UNDETERMINED** | aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.ne: scalar identity/structural comparison looks plausible, but no pinned P7 declaration for this Aspis derive and no proved relation between the source newtype/record and kit carrier. Actual derive expansion, nested limb comparison including noncanonical representatives, panic/error freedom and unchanged borrow ownership require association. No fresh native derive differential; std u8 equality fixtures do not cover this model. |
| 2 | `XRo_Join_Carriers.E.Challenges` (XRo_Join_Carriers.lean:24) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.Challenges is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 3 | `XRo_Join_Carriers.C.D` (XRo_Join_Carriers.lean:17) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.D is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 4 | `XRo_Join_Carriers.E.D` (XRo_Join_Carriers.lean:30) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.D is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 6 | `XRo_Join_PowersLoop.E` (XRo_Join_PowersLoop.lean:7) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_PowersLoop.E is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 8 | `XRo_Join_Carriers.E.Err` (XRo_Join_Carriers.lean:31) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.Err is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 10 | `XRo_Join_Carriers.C.Point` (XRo_Join_Carriers.lean:10) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.Point is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 11 | `XRo_Join_Carriers.E.Point` (XRo_Join_Carriers.lean:23) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.Point is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 12 | `XRo_Join_Carriers.C.Prepared` (XRo_Join_Carriers.lean:16) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.Prepared is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 16 | `XRo_Join_Carriers.C.ST` (XRo_Join_Carriers.lean:13) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.ST is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 18 | `XRo_Join_Carriers.C.Sem` (XRo_Join_Carriers.lean:12) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.Sem is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 19 | `XRo_Join_Carriers.E.Sem` (XRo_Join_Carriers.lean:25) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.Sem is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 22 | `XRo_Join_Carriers.C.T` (XRo_Join_Carriers.lean:14) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.T is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 23 | `XRo_Join_Carriers.E.T` (XRo_Join_Carriers.lean:27) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.T is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 24 | `XRo_Join_Carriers.C.V` (XRo_Join_Carriers.lean:9) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.C.V is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 27 | `XRo_Join_Carriers.E.View` (XRo_Join_Carriers.lean:28) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.E.View is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 28 | `XRn_Join_Wide` (XRn_Join_FieldExternal.lean:47) | 0 | Aspis carrier/type (mislabelled library) | **UNDETERMINED** | XRn_Join_Wide is a representation/alias, not an external std function. Missing a source/adopted-carrier association for its uses; P7 cannot establish Aspis nominal-carrier identity. |
| 30 | `XRn_Join_basis` (XRn_Join_MaskModel.lean:6) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_basis is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 32 | `XRn_Join_dotFinish` (XRn_Join_DotModel.lean:30) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_dotFinish is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 33 | `XRn_Join_dotZero` (XRn_Join_DotModel.lean:36) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_dotZero is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 36 | `XRn_Join_fromFnState` (XRn_Join_ABI.lean:29) | 0 | from_fn state ABI | **UNDETERMINED** | L006 proves exact state-threaded indexed traversal, including fail/div. Rust external-capture restoration and partial-initialisation/closure Drop effects are not represented/proved. R002 observes final16, ascending indices and panic cleanup, not an arbitrary-effect refinement. |
| 38 | `XRn_Join_iterator` (XRn_Join_StdExtra.lean:10) | 0 | IterMut Iterator dictionary | **UNDETERMINED** | Its next is XRn_Join_next, which drops the P7 item-restoration continuation. A borrowed T carrier/callback law justifying this projection is missing; no mutation-complete association. |
| 39 | `XRn_Join_mapArray` (XRn_Join_TerminalModel.lean:37) | 0 | pure carrier-map helper | **UNDETERMINED** | Pure List.map conversion, not Rust array::map/FnMut. No error, callback-state or Drop carrier is present; use only as a proved carrier adapter, not a standard-library refinement. |
| 40 | `XRn_Join_mpow` (XRn_Join_ByteFields.lean:37) | 0 | Aspis power stand-in (mislabelled library) | **UNFAITHFUL** | Retained KSA failure: exponent2 at base2 yields1, square is4. Not a std/core item. Correct with raw emitted power/fixed-chain inverse association; KSA_FINDING failure matrix and KSA_L002, not newly replayed. |
| 41 | `XRn_Join_nativeAfter` (XRn_Join_TerminalModel.lean:16) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_nativeAfter converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 42 | `XRn_Join_nativeLive` (XRn_Join_TerminalModel.lean:8) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_nativeLive converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 43 | `XRn_Join_nativePublic` (XRn_Join_TerminalModel.lean:22) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_nativePublic converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 44 | `XRn_Join_nativeQ` (XRn_Join_TerminalModel.lean:35) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_nativeQ converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 45 | `XRn_Join_nativeTransition` (XRn_Join_TerminalModel.lean:19) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_nativeTransition converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 46 | `XRn_Join_newError` (XRn_Join_TerminalModel.lean:43) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_newError converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 47 | `XRn_Join_next` (XRn_Join_StdExtra.lean:6) | 0 | IterMut next ABI projection | **UNDETERMINED** | L004 next_projection is EXACTLY projection of P7 next and discards its writeback continuation. No connection from arbitrary yielded mutable-reference updates to original slice. Projection equality is not mutable next fidelity. |
| 48 | `XRn_Join_nextBackPair` (XRn_Join_ABI.lean:22) | 0 | IterMut next_back ABI | **UNFAITHFUL** | L002: after P7 next on [7], state i=1; this returns Some7. Native R002 returns None. Replace underlying mutable next_back reset index0 with current s.i, then prove/retain full restoration chain. No product-path reachability claim. |
| 49 | `XRn_Join_oldAfter` (XRn_Join_PublicModel.lean:15) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_oldAfter converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 50 | `XRn_Join_oldChallenges` (XRn_Join_TerminalModel.lean:39) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_oldChallenges converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 51 | `XRn_Join_oldLive` (XRn_Join_PublicModel.lean:7) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_oldLive converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 52 | `XRn_Join_oldPublic` (XRn_Join_PublicModel.lean:21) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_oldPublic converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 53 | `XRn_Join_oldTransition` (XRn_Join_PublicModel.lean:18) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_oldTransition converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 54 | `XRn_Join_partial` (XRn_Join_DotModel.lean:8) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_partial is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 55 | `XRn_Join_powers` (XRn_Join_DotModel.lean:37) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_powers is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 56 | `XRn_Join_preparedPart` (XRn_Join_DotModel.lean:44) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_preparedPart is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 57 | `XRn_Join_q` (XRn_Join_ByteFields.lean:8) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_q is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 58 | `XRn_Join_qBytes` (XRn_Join_ByteFields.lean:28) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_qBytes is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 59 | `XRn_Join_qpow` (XRn_Join_CircleModel.lean:5) | 0 | Aspis power stand-in (mislabelled library) | **UNFAITHFUL** | Retained KSA failure: exponent2 at base2 yields1, square is4. Not a std/core item. Correct with raw emitted power/fixed-chain inverse association; KSA_FINDING failure matrix and KSA_L002, not newly replayed. |
| 60 | `XRn_Join_raw` (XRn_Join_DotModel.lean:9) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_raw is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 61 | `XRn_Join_releaseQ` (XRn_Join_TerminalModel.lean:36) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRn_Join_releaseQ converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 63 | `XRn_Join_reverseNext` (XRn_Join_ABI.lean:14) | 0 | Rev next ABI | **UNFAITHFUL** | L010 reverse_repeats_spent: Rev around i=1/[7] returns Some7 instead of None (R002 native). Delegates to index-reset mutable next_back. Fix that dependency; preserve/retain both returned back continuations. L010 also checks singleton changed-item writeback and empty case. |
| 64 | `XRn_Join_scaleQ` (XRn_Join_MaskModel.lean:12) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_scaleQ is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 66 | `XRn_Join_sliceRange` (XRn_Join_DecodeModels.lean:55) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_sliceRange is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 67 | `XRn_Join_sub64` (XRn_Join_DotModel.lean:7) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_sub64 is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 68 | `XRn_Join_toQ` (XRn_Join_DotModel.lean:34) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_toQ is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 69 | `XRn_Join_u64` (XRn_Join_DotModel.lean:21) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_u64 is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 73 | `XRn_Join_wrap64` (XRn_Join_DotModel.lean:6) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_wrap64 is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 83 | `XRo_Join_PreparedBoundaries.boundaries` (XRo_Join_PreparedBoundaries.lean:25) | 0 | Aspis dictionary/helper (mislabelled library) | **UNDETERMINED** | XRo_Join_PreparedBoundaries.boundaries assembles a dictionary/selects a result or defines a test Copy instance. Missing emitted/adopted dictionary association, not a Rust std fidelity obligation. Do not infer closure from projection/slot equalities. |
| 84 | `XRo_Join_PreparedBoundaries.cachedClaim` (XRo_Join_PreparedBoundaries.lean:11) | 0 | Aspis dictionary/helper (mislabelled library) | **UNDETERMINED** | XRo_Join_PreparedBoundaries.cachedClaim assembles a dictionary/selects a result or defines a test Copy instance. Missing emitted/adopted dictionary association, not a Rust std fidelity obligation. Do not infer closure from projection/slot equalities. |
| 86 | `XRo_Join_Carriers.cc` (XRo_Join_Carriers.lean:42) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.cc converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 88 | `XRo_Join_Carriers.ce` (XRo_Join_Carriers.lean:68) | 0 | Aspis carrier adapter (mislabelled library) | **UNDETERMINED** | XRo_Join_Carriers.ce converts/projections Aspis fields. Roundtrip alone is not source association, adopted installation or full effects/error transport. No Rust std item or P7 body corresponds to this nominal adapter. |
| 89 | `XRo_Join_PowersLoop.chosen` (XRo_Join_PowersLoop.lean:8) | 0 | Aspis dictionary/helper (mislabelled library) | **UNDETERMINED** | XRo_Join_PowersLoop.chosen assembles a dictionary/selects a result or defines a test Copy instance. Missing emitted/adopted dictionary association, not a Rust std fidelity obligation. Do not infer closure from projection/slot equalities. |
| 90 | `XRn_Join_Bytes.chunksValid` (XRn_Join_FunsExternal.lean:422) | 0 | Aspis arithmetic/byte/source helper (mislabelled library) | **UNDETERMINED** | XRn_Join_Bytes.chunksValid is an Aspis helper rather than a Rust std/core external. No unique documented std function exists for this body; source/body or explicit adapter association remains required. No P7 citation or passing fixture can replace that association. |
| 91 | `XRo_Join_Nonvacuity.copyUnit` (XRo_Join_Nonvacuity.lean:7) | 0 | Aspis dictionary/helper (mislabelled library) | **UNDETERMINED** | XRo_Join_Nonvacuity.copyUnit assembles a dictionary/selects a result or defines a test Copy instance. Missing emitted/adopted dictionary association, not a Rust std fidelity obligation. Do not infer closure from projection/slot equalities. |

## Final verification and handoff

Used **15/80 Lean attempts** (9 exit0, 6 rejected), **3/10 Rust attempts**
(2 exit0, 1 setup failure), **0 Kani**. Budget remains; stopping because the
assigned table is complete with explicit unresolved obligations, not because
those obligations were discharged. `KSC1_VERIFICATION.json` checks all current
new module hashes against exit0 compiler snapshots and finds zero errors.
All **23 new theorem roots** co-import in `KSC1_FinalAudit.lean` and print only
subsets of `[propext, Classical.choice, Quot.sound]`. The first failed elaborations'
sorryAx diagnostics are retained and excluded. No sorry/admit/axiom/native_decide
occurs in current KSC1 source. `KSC1_proof_provenance.json` independently verifies
the reused generic state-traversal proof differs only by names/import/comment.

Final target **KSC1_L015**, `KSC1_FinalAudit.lean`: exit0,
wall2.8996351810055785s, peakRSS2635332KiB, swap0,
source revision `e6c42a30f88f81c1ff5dc7b6c3550f4ec8d67591` plus the exact dirty source SHA256
in its receipt. Final root `KSC1.Final.singleton_counterexample` has exactly
`[propext, Classical.choice, Quot.sound]`. Lean total wall
38.81330850010272s; maximum attempt RSS2653280KiB;
total swap0. Every target/argv, source revision/hash, dependency/object pins,
exit, wall, RSS, swap and complete axiom line is in KSC1_attempts.jsonl and
its original per-attempt receipt/stdout/time/snapshot files. R003 has the final
branch coverage and stricter frozen-manifest/resolved-edge validation; its
optimized native run exits0, wall1.0429558230098337s, peakRSS147096KiB, swap0.

Every scope verifies MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64;
Lean uses -j1/-M7000, native uses explicit -O. All admission receipts have
exit0 AND allowed:true, with no transport/admission retry. No other job's scope
or worktree was modified. The 236 resolved Aeneas object hashes match the final
preflight pins at terminal check. No owned scope remains. The persistent cache
`/home/dombarker/project-offloads/codex-cx-libmodel1-cache-20261027` and private
Lean objects are retained. Only the job's compiled native diagnostic executable
was removed; its hash/size are recorded in KSC1_terminal_state.json.

Discharged: exact P7 eq/ne identities, Vec shared emptiness law, indexed
state-traversal identities and the stated small fixtures/counterexamples.
Retained: P7, SDK/runtime trust, every headline/source-to-artifact premise,
borrow/callback/drop/trace/adopted-path/source-association obligations listed in
the table. Release premises removed/added/changed: **0/0/0**. No cryptographic
hypothesis, metric, adversary, game or frozen3 model changed. No full frozen
manifest, Kani, SBF rebuild or unrelated regression was run. No shipped file
or cfg(kani) module changed, so ELF rebuild was not triggered. Inherited pins,
not newly rebuilt:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Next concrete deliverable: KSB's corrected raw-body kit should replace the
index-reset mutable next_back, prove its legal restoration invariant, then
recheck affected wrappers and their kernel dependency consumers. The remaining
UNDETERMINED rows need the exact per-row associations/effect relations listed
above. No general library-model closure or emission credit follows from this
packet. The deployed 100-bit target and S2 remain **not established**.

All commits are local; no push/merge, key/wallet action or other-worktree edit.
Source/document whitespace checks exclude unmodified raw tool logs, whose
original trailing whitespace is intentionally retained as evidence.
