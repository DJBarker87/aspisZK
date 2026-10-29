# Complete-cone condition: rejected for V229 and V230

This is a **negative static qualification check**, not a positive purity
certificate, a source-binding proof, a native value differential, or a
witness-dependent privacy finding. Both requested roots contain a mandatory
external-state-reading callee. One such path suffices to refute a universal
condition over the complete call cone; no assumption of purity is made at an
unexamined foreign-function edge.

The read-only capture in `static-capture.json` pins 44 complete source files
(six application/configuration files and 38 rust-src 1.94.1 files), their byte
lengths and SHA256s, application git blobs, exact rustc version, inherited
deployed feature-unit graph and lockfile, and raw runtime disassembly. The
application files were checked byte-for-byte against this branch's HEAD.
`tools/pv-owne-20261029/static-check.py` repeats the identity and mandatory-path
checks. It is a rejection checker, not an automated proof of purity or a
complete source-to-model correspondence checker.

## Mandatory path common to both rows

1. `pair_forest_hiding.rs:184–195`,
   `pool_v1_pair_forest_copy_active_rows_v1()` (V229/op133), unconditionally
   calls `build_pool_v1_pair_forest_copy_row_schedule_v1()` before collecting,
   sorting or deduplicating endpoints.
2. `pair_forest_hiding.rs:198–205`,
   `pool_v1_pair_forest_copy_active_row_masks_v1()` (V230/op134), initializes
   its local mask array and unconditionally calls that V229 root.
3. The forest builder at `pair_forest_hiding.rs:119–181` first calls
   `build_pool_v1_pair_copy_row_schedule_v1()`; no filter, error return,
   iterator step or endpoint check precedes this call.
4. `pair_tree_hiding.rs:105–107` starts that legacy builder with
   `Vec::with_capacity(POOL_V1_PAIR_COPY_ROW_LINKS_V1)`, with constant capacity
   127. The Link has u16 fields and is non-zero-sized. The inherited pinned
   1.94.1 layout/native evidence gives size8/alignment2, request1016/alignment2
   (`../pv-ownd-20261029/native-result.json`, `native-01/output.log`). This
   historical measurement remains supporting finite validation only.
5. rust-src `alloc/src/vec/mod.rs:525–526,966–967` delegates to
   `RawVec::with_capacity_in`; `alloc/src/raw_vec/mod.rs:175–179,417–455`
   computes a positive layout and invokes `alloc.allocate(layout)` before
   returning any initialized Link. It does not return a no-allocation empty
   carrier for this non-ZST positive capacity.
6. `alloc/src/alloc.rs` selects the runtime arm of `const_eval_select`, then
   `Global::alloc_impl_runtime:185–195`, `alloc:89–97` and `__rust_alloc`.
   `std/src/alloc.rs:450–456`'s default entry point `__rdl_alloc` calls
   `System.alloc`. `std/src/sys/alloc/mod.rs` selects Unix and MIN_ALIGN16
   for x86_64; `std/src/sys/alloc/unix.rs:8–15` calls
   `libc::malloc(layout.size())` for the 1016/2 request.
7. The retained deployed-client binary's `__rust_alloc` at ELF address
   `0x89b90` jumps to `__rdl_alloc` at `0x1cdc20`. That entry point's
   ordinary-alignment branch at `0x1cdc37` jumps through
   `malloc@GLIBC_2.2.5`. This establishes which existing default allocator
   the retained client uses; it is not a new proof of correspondence of the
   original statement functions to that binary. The binary also contains
   prover-local `host_forest` copies; those are not substituted for the
   requested original statement bodies in this check.
8. The build host's glibc2.39 `__libc_malloc` reads allocator state *before*
   returning a successful allocation. At `0xad764`,
   `cmpb $0x0,0x15da1d(%rip)` reads the initialization-state byte at ELF
   address `0x20b188`. On the initialized positive-size path, at `0xad79a`,
   `mov %fs:0x0(%r13),%rdx` reads **thread-local allocator state**. The full
   disassembly is retained, including its branches and further TLS reads.
   These are not reads of a freshly created function-local Link or mask.
   The captured instruction at `0xa9e7b` writes1 to the same global byte;
   readelf places it within writable `.bss`, confirming its mutability.

The runtime binary identities captured read-only are:

| File | SHA256 |
|---|---|
| retained `client-deployed-baseline` | `fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348` |
| host `/lib/x86_64-linux-gnu/libc.so.6` | `3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf` |

The baseline configuration remains rustc1.94.1, release opt3,
debug_assertions/overflow_checks off, panic unwind, client features
`r1p-check,aspis-r1-cost-probe/ct-host-prover`; the per-unit feature lists are
captured from the inherited frozen graph. No binary was built or executed
this round, and no new deployed value/fingerprint equivalence is claimed.

## Review of the other explicitly requested source stages

The following reviews do not repair or remove the mandatory external read.
They identify the actual library code instead of treating `collect`, sort,
or dedup as opaque deterministic specifications.

| Stage | Bodies reviewed in the pinned source capture | Result relevant to qualification |
|---|---|---|
| Application schedule and `link` | legacy/forest builder, both `link` constructors, both `endpoint_counts`, legacy/forest path-base helpers, membership-block helper, profile constants | Fixed constants; local Link construction; local two-array counter loops; local Shape/EndpointCapacity Result branches. Initial allocation precedes these loops. |
| Source iterator and filtering | Vec `IntoIterator`, `IntoIter::{next,size_hint,fold,try_fold,Drop,forget_allocation_drop_remaining}`, slice Iter/IterMut and macros; Filter constructor, predicate, fold/try_fold and SourceIter | Pointer/cursor and owned-field reads; the concrete predicate only reads Link kind. Drop reaches RawVec/deallocation. No purity is inferred for allocator calls. |
| `flat_map` | Iterator::flat_map, FlatMap, Map, FlattenCompat/Fuse constructors, next, size_hint, fold/try_fold; `[u16;2]` IntoIterator and PolymorphicIter | Capturing closure only reads producer/consumer fields. Flatten keeps front/back Option state and uses nested folds; array iteration tracks its live local range. No environment or random seed is supplied. |
| `collect` | Iterator::collect, Vec FromIterator, SpecFromIter, SpecFromIterNested, in_place_collect selection and both collect bodies, InPlaceDrop, InPlaceDstDataSrcBufDrop, SpecExtend, SetLenOnDrop, Vec extend paths | Includes specialization choices and fallback, stores, length/cursor guards, source detachment, shrink/error and cleanup calls. Legacy Filter can collect in place; FlatMap has nested/fallback collection machinery. No generic correspondence result is asserted. Any allocation/shrink/drop primitive retains its external runtime cone. |
| reserve/push/growth | Vec reserve/push; RawVec reserve, grow_amortized, finish_grow, allocation/error/drop; Global allocate/grow/shrink/deallocate | Capacity arithmetic and initialized-memory transport do not eliminate calls to malloc/realloc/free. Allocation success depends on runtime state. |
| `sort_unstable` | slice entry; unstable::sort/ipnsort; find_existing_run; quicksort, pivot::choose_pivot/median3/median3_rec, cyclic and fallback partitions and gap guards; heapsort/sift_down; small-sort type dispatch, insertion, network, merges and CopyOnDrop | u16 comparator is scalar order. Pivots sample fixed positions derived from length (pseudomedian, not external randomness). Scratch is stack-local. Pointer arithmetic, swaps, moves and invariant aborts are present; no external random seed or clock was found in these bodies. This is inspection, not their missing own-1 store/carrier proof. |
| `dedup` | Vec::dedup/dedup_by, first-duplicate search, FillGapOnDrop, same_bucket, copy/drop, set_len/forget | u16 equality, cursor reads, local copies and drops. Guards and unwind continuation retained in review. No allocator/panic runtime purity is assumed. |
| mask fold | original masks root, usize conversion/index/shift, u16 shift/OR, local64-array update, Vec IntoIter/drop | Operands derive from each local row; source-to-model usize/u16/array binding remains the inherited own-1 obligation. Iteration destruction reaches deallocation. |
| allocator and abort entry points | Global runtime methods, alloc/dealloc/realloc, default __rdl entry points, System Unix allocation; raw_vec handle_error; std rust_oom/default hook | Success-path TLS read is decisive. Separately, rust_oom at std/src/alloc.rs:425 loads the mutable static HOOK; its default hook may request backtrace/diagnostic behavior. That failure branch remains under rdea-1 and is **not** the decisive obstruction. |

This review rejects the complete-cone condition at a concrete mandatory
callee. It does not assert an exhaustive clean call graph for arbitrary
libc internals or panic diagnostics, and does not need to traverse them
after the counterexample to qualification has been identified.

## Allocation and rdea-1

The first source-level allocation request is fixed1016/alignment2 under the
pinned layout; abort on failure and primitive runtime behavior stay under
rdea-1. The old own-1 allocation/drop and resource/value work is preserved.
However, own-2's qualification says **no thread-local read over the complete
call cone**, and the user's explicit instruction says **any external read**
requires stopping that row. Neither text states an exception for the normal
successful allocator's TLS accesses. Clause(c) expressly covers allocation
failure; it does not itself erase a successful malloc TLS read from the
qualification condition. This check therefore does not silently apply a
runtime-quotiented version of own-2.

This is not a proof of witness-dependent allocation sizes, event order or
abort, and is not a D159 leak FINDING. It is an exact reason the proposed
singleton-domain evidence class cannot be assigned under the stated rule.
V229 and V230 remain SUSPENDED under own-1, with their prior source binding
obligations intact. V228 is not reclassified or withdrawn by this task.
