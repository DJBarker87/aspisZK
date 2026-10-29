# D439 whole-cone influence check

This applies to the original statement roots V229/op133 and V230/op134,
not the different `aspis_prover::host_forest` implementations. The two roots
have no arguments. All three schedule/profile source blobs equal this branch.
`static-capture.json` records the revalidated 44-file source cohort and 49
host inputs, 14 compiled ordinary-computation functions, all 74 inter-function
call/jump edges, and 63 RIP-relative references. The compiled frontier is a
supporting selection/completeness check; source reasoning is given below.
No compiler-preservation claim is inferred from disassembly.

## Classifications and completeness

The source inventory is the complete text capture in
`../pv-owne-20261029/static-capture.json`, re-hashed by this task's checker.
Its old rejection conclusion is superseded by D439. Classifications:

| Reached stage | Bodies and influence channels |
| --- | --- |
| Application | Both roots; forest and legacy schedule builders; Link constructors; endpoint_counts; path/membership/profile helpers. All values are constants or derived local fields. Checked layout errors return a local enum. No callback, environment, syscall, mutable static, TLS or errno access. |
| Iterator construction and iteration | IntoIterator for Vec and array; IntoIter next/fold/try_fold/size_hint, Filter predicate, Map, FlatMap/FlattenCompat/Fuse, array PolymorphicIter, slice iterator macros. Reads only owned Links, u16 arrays, iterator front/back cursors and length/state. Closures are statically selected, not external function-pointer inputs. |
| Collection and cleanup | FromIterator -> SpecFromIter/SpecFromIterNested; in_place_collect, InPlaceDrop, InPlaceDstDataSrcBufDrop; SpecExtend; SetLenOnDrop; Vec push/extend/reserve/from_parts/set_len; RawVec allocation/growth/drop. Fields, arithmetic, memory copies and allocator operations only. Link/u16/array elements have no destructor accessing external state. Remaining source destruction releases its allocation. |
| Sort | slice sort_unstable -> ipnsort; find_existing_run; quicksort/partition implementations; choose_pivot/median3/median3_rec; heapsort/sift_down; small-sort dispatch/network/insertion/merge guards. Comparator is u16 scalar `<`. Pivot selection uses length and fixed offsets, with no randomized seed. Scratch is stack memory. |
| Dedup | Vec dedup/dedup_by, first-duplicate scan, FillGapOnDrop, copy/set_len/forget. Comparator is scalar u16 equality; drop of u16 is empty. No external observer callback. |
| Masks | Initialize 64 zero u16s, iterate local rows, row-to-usize conversion, /16, %16, shift and OR, current-array read/store, Vec destruction. Only local data. |
| Allocator | __rust_alloc, __rust_realloc, __rust_dealloc, including everything below them: D439(2) black box. Internal malloc globals, TLS, single-thread state and errno save/restore are allowed. Success/failure retained as rdea-1; addresses treated below. |
| Memory operations | memset, memcpy, memmove, memcmp/bcmp if lowered: D439(1), effects confined to supplied regions, retained at V370. The four observed memset calls initialize caller stack arrays. No external information is supplied by their functional semantics. Their runtime implementation/codegen is the expressly retained boundary. |
| Allocation shim | __rust_no_alloc_shim_is_unstable_v2 is an additional unlisted callee. The selected body is a return, with no memory read or observable effect. Classify as constant/local computation, not external information. |
| Arithmetic/ptr intrinsics | Layout checks, usize/u16 scalar operations, non-null construction, pointer add/difference, moves and byte copies. Operands are constants or owned fields; memory semantics are at V370. No new entropy or process state. |

All compiled indirect calls are GOT-resolved or the four explicitly resolved
memset register calls; the checker rejects any unclassified edge. Every RIP
reference outside the cut is `.rodata`, `.data.rel.ro` or a resolved `.got`
slot. No `%fs`/`%gs` instruction occurs there. Relocation slots and immutable
panic-location constants are not mutable process inputs. Source review covers
inlined code and the possible specialization/fallback paths, not just symbols.
No randomness, IO, clock, environment or errno-returning API is invoked.

## Panic, error, failure and unwind edges

We do not classify the panic runtime as pure: it can read a mutable hook and
perform IO. Its edges must be unreachable for this computation, or be an
allocation-failure event retained under rdea-1.

* Both endpoint checkers short-circuit `row >= 1024` before array access;
  otherwise each u8 count is incremented only below 2. Returning a Shape or
  EndpointCapacity enum requires no external state. Fixed schedule helper
  ranges are 0..21 and 0..20. Link endpoints stay below 1024. Existing named
  schedule/result/bounds lemmas certify these scalar facts.
* V230 receives the checked rows; `row/16 < 64` and `row%16 < 16`. Thus neither
  bounds panic nor shift failure is entered. The named block/shift lemmas are
  reused by the new literal theorem. The actual maximum row is 1018.
* Collector's TrustedLen guard tests exhaustion/capacity consistency, not
  external state. A fixed-size `[u16;2]` for each of 136 Links emits exactly
  272 words. The guarded iterator cannot overproduce. In-place Filter emits
  at most one Link per consumed Link; Link/u16 are non-ZST. `needs_realloc`'s
  alignment panic has equal source/destination alignment2; debug-only checks
  are disabled in release. FlatMap selects the separately allocated path in
  this cohort (checked compiled frontier), whose reserve arithmetic is bounded.
* Sort's ordering panic requires inconsistent comparison; ordinary u16 `<`
  is a strict total order. Its pivot/partition and small-sort abort guards
  are internal length/index preconditions, preserved by slice partitioning,
  fixed pivot offsets and the dispatch thresholds. They introduce no new
  influence channel even as guards: their conditions derive from local
  lengths, values and same-allocation offsets. The order panic cannot occur
  with this comparator. No fallible/custom comparison/destructor can unwind.
* Capacity-error branches require exceeding isize::MAX or layout arithmetic
  bounds. The largest live request here is 2032 bytes/alignment2, so these
  cannot occur. Null allocation is the remaining failure, retained with its
  actual hook/abort behavior under rdea-1, not asserted deterministic or pure.
* `_Unwind_Resume` appears only in cleanup landing pads for the preceding
  panic edges. It is not an extra entropy source reachable on normal returns;
  no ordinary user destructor can raise an exception. Failure diagnostics
  remain under rdea-1. No blanket exception for arbitrary panic/IO is used.

These guards are local and address independent, so ruling out their failure
is not conditional on one allocator-chosen address. Source safety/library
semantics and their codegen remain V370; no source-to-machine equality axiom
is introduced. The harness result will also check the one constant successful
execution rather than substitute another model for a missing source law.

## Address independence over the entire ordinary cone

Assign each live allocation its own base B, length/capacity and initialized
indexed elements. A pointer is `(allocation, element offset)`. Replace B by
any other valid, correctly aligned base, retaining contents and layout:

1. Application constructors, counters, translation, mask indexing and all
   scalar comparisons do not inspect pointers.
2. Vec/array/slice iteration compares front and end from the same allocation;
   equality is equality of offsets. Difference/size_hint is the difference
   of offsets. For these non-ZST types no synthetic ZST-address length is used.
3. Collector sink offsets and source consumption determine every read/store.
   `src.ptr != src_ptr` compares one allocation at two iterator positions;
   its body contains only disabled debug checks. Allocation alignment and
   size-ratio dispatch depend on types, not returned addresses. Grow/shrink
   transports indexed contents, capacity and length, never hashes/casts the
   numerical base into a value. Success/null is channel(i).
4. Sorting's `region.as_ptr() != v_base` distinguishes the first region from
   the offset len/2 region of one slice. len/2 is positive when tested. Merge
   comparisons (`left < left_end`, consumed-pointer equality), insertion
   cursor bounds and pivot pointer subtraction all use one allocation and
   cancel its base. Sorting compares elements using u16 order, never address
   order across allocations. Stack scratch and heap regions are copied by
   index; no cross-region numerical address comparison selects an output.
5. Dedup's read/write cursor, FillGapOnDrop and IntoIter drop use same-buffer
   offset equality/difference and lengths. Drop of Link and u16 is empty;
   raw deallocation passes the address back into the black box.
6. All selected pointer casts are type casts, or the above offset/length
   operations. No absolute pointer-to-integer value, pointer hash, arbitrary
   allocation-order comparison or address-dependent branch feeds the result
   or caller control. Scalar booleans cast to usize in sort are comparison
   results, not pointers. Caller-memory primitive semantics are covered by
   D439(1)/V370; their internal implementation is not silently re-proved.

Induction over iterator/collector/sort/dedup steps therefore preserves indexed
contents and identical guards and requests after any valid base replacement.
The new Lean address lemmas check the cancellation/order algebra; the mapping
from source operations to these cases is this explicit source argument.
They are not claimed to be a full Rust operational-semantics refinement.

## Channel (iii)

Outside the permitted primitives/allocator no mutable global, TLS, errno,
external handle, environment, time or IO result is read. The only read sets
are owned initialized memory, immutable constants and iterator/local metadata.
Allocator writes to its private/process state are disjoint from this set.
It can write a returned memory region as part of allocation/resize; only
initialized application elements are subsequently read (constructors initialize
Links, copied elements retain their initialization, endpoint arrays are zeroed,
and all masks start at zero). Padding/uninitialized spare capacity is never
read as a value. This closes channel(iii); errno inside free stays inside the
black box. Valid realloc is content-preserving at the retained runtime boundary.

Qualification under D439 passes for both roots, with rdea-1 and V370 retained.
This is a whole-cone influence/source argument plus a checked static frontier,
not the missing own-1 byte-memory structural binding. Restoration still needs
the named value literals and deployed-configuration harness results.
