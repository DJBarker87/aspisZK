# S6 owned allocator reference: extraction and source-helper composition

Whole S1/S2/S6 and the100-bit target remain OPEN. No concrete enclosing
SDK/source trust premise is removed. This closes the previously missing
owned-Rust-reference → emitted Lean → arithmetic induction connection, then
consumes it in the ORIGINAL complete snapshot helper interface.

## What is now proved

1. `S6BumpOwnedReferenceSourceV1` contains the actual Aeneas-emitted owned
   `step` and actual emitted Option Try/FromResidual bodies. Its Rust body is
   copied VERBATIM from the reference already checked against the actual SDK
   BumpAllocator in `f41698a231`. Native Kani evidence is reused, not rerun.
2. `S6BumpReferenceExactV1.step_total_exact` proves that COMPLETE emitted
   function is TOTAL for every Usize input and nonzero alignment. Its Option
   output, including insufficient-capacity/header rejection, equals the
   existing natural-number step after selecting the initial cursor. Checked
   subtraction rejection is caught as None, division is nonzero, and the
   product after floor division cannot overflow. There is no successful-child
   or reference-equivalence premise.
3. `S6BumpReferenceReserveV1.reserve_total_exact` composes finite lists of
   those SAME emitted steps. The complete Result remains total, including
   the exact first rejection. `reserve_fits` consumes the earlier arithmetic
   induction:8 plus the sum of(bytes+7) suffices when each alignment is1..8.
   No per-step success/totality law is assumed.
4. `S6SnapshotSourceAllocatorV1` installs the concrete owned SOURCE reference
   in the EXISTING `Allocator Usize` interface, with alignment1 for snapshot
   Vec bytes and no-op cleanup. `reserve_eq` proves complete Result equality
   between the ORIGINAL reservation and the emitted-step sequence; None is
   mapped to outer panic. Nat-to-Usize conversion is exact on bounded requests.
   `admitted_bounds` derives those bounds from the actual three source slots.
   `allocate_snapshots_total` proves the ORIGINAL `allocateSnapshots` returns
   `(next,entry.heap)` for EVERY COMPLETE Entry at cursor262144, with
   next.val≥200180 and next.val−8≥200172. No accepted execution, valid metadata,
   distinct handles, canonicality, allocation success or abstract allocator
   law is a hypothesis.

The final bound is conservative: it allows up to7 bytes rounding for each
snapshot request even though their source-reference alignment is1. The
cursor offset includes the reserved8-byte header; usable bytes are therefore
reported separately. No deallocation refund or live-byte reuse is assumed.

These are TOTAL extracted-source/reference arithmetic results. The exact
account heap is retained, including errors/metadata/handles/aliasing. This is
not a simplified SDK/account carrier or a replacement for stage1.

## Source interpretation and normalization

The initial extraction left Option control-flow helpers opaque. The next
Charon command explicitly includes their ACTUAL Rust bodies. No custom axiom
or handwritten Option-result replacement is installed. The existing checked
`S6StdOptionSourceV1.optionDiscriminant` instance is reused; its source is
retained and the direct imported object is pinned.

The sole remaining external call in the emitted step was the monomorphic
`core::mem::size_of::<usize>()`. The source normalizer resolves ONLY that call
to8 from Charon's exact x86_64 target metadata. It does not define a fake
generic size_of for arbitrary types. The native aarch64 Kani predecessor
separately asserts usize size8. This is a source intrinsic interpretation
qualified by the word-size/target pins, not a fresh cross-architecture native
allocator or SBF-layout certificate.

Other normalization removes an independently checked empty Types import and
the now-unused external-template import, and removes the backend's automatic
heartbeat/recursion overrides so checked source runs with DEFAULT resources.
Exact raw Funs text, normalized text/hash, every rewrite and appended axioms
audit are retained. The unfilled axiom template is NOT imported or exported
as an accepted proof. Raw generated Funs text is evidence only, never compiled.

The existing native one-step certificate and this extraction share exactly
the same Rust reference body. The Kani certificate remains scoped to a valid
262144-byte arena, initial cursor0 or8..262144, request1..262144 and alignment
1/2/4/8, using its ordinary successful arena-provider malloc model. The
source theorem is stronger on pure word arithmetic; it does not expand the
native memory-domain certificate. No new native Kani verification was run.

## What remains owed

The concrete reference Allocator instance is NOT claimed to select the actual
native global allocator, prove native entry admission, or account for all
allocations before/after snapshots. The actual entrypoint/metadata Vec prefix,
decoder Boxes, later verifier allocations, runtime/caller effect association
and source/compiler-to-release-artifact join remain explicit. Box ownership,
cleanup and native field projections retain their existing scoped packets;
they are not discharged by this arithmetic theorem.

S6's enclosing accepted-only reuse theorem from `f41698a231` still requires
the S2 owner's concrete accepted stage1 source instance. It does NOT require
proving every native allocation succeeds. S1's preparation/data and primitive
instances are now explicitly lead-owned per the latest handoff; this job does
not duplicate them. An available independent next S1 connection is the
original nested borrowed-claim → owned helper/caller correspondence, for which
older focused step sources/caches should be reused before new native checks.

No production Rust, protocol parameter, security contract or ELF changes were
made. The reviewed ledger at research revision
`fd250f21844ecba47b3431ee533f9ae3e17cd1ad` retains default/devnet source
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` and the existing ELF pins.
The SDK implementation is the same release-lock/checksum-pinned2.3.0 source
from the predecessor packet. Final native/SBF/caller re-pins remain owed;
these reference files do not adopt a changed production allocator. No source
or security-contract decision is requested by this packet.

## Validation

| Focused target | Exit | Wall seconds | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|
| S6BumpOwnedReferenceSourceV1 |0|11.390701958|2184773632|0|
| S6BumpReferenceExactV1 |0|38.284001166|2162556928|0|
| S6BumpReferenceReserveV1 |0|30.117919459|2745925632|0|
| S6SnapshotSourceAllocatorV1 |0|22.971129375|3229466624|0|

All11 accepted #print axioms reports are standard-only (one has no axioms).
Each smallest changed target ran locally and sequentially under the atomic
lock, -j1 -M4400, with exact source/tool/direct-import pins and reused warm
dependencies. No unchanged full manifest or native runtime replay was run.

The final Charon extraction passed in0.165320452s/132880KiB process RSS;
scope peak304959488 bytes,1GiB max/896MiB high/SwapMax0. Aeneas passed in
0.684342655s/61072KiB process RSS; scope peak226140160 bytes,512MiB max/
448MiB high/SwapMax0. Both fresh admissions passed and all pressure/OOM
counters are0. Time is in tiny optimized reference compilation/translation,
not certificate generation or aggregation.

An intervening1GiB Aeneas admission was denied before launching any scope.
The later512MiB translator scope uses streamed tool hashes rather than
materializing rustc_driver. Its admission retains the SAME min57GiB/
MemTotal−5GiB total cap budget and requires MemAvailable to cover ALL unused
finite cap headroom plus1GiB additional free reserve. Other jobs/caps were
untouched. Prior translator RSS was60MiB; the earlier larger scope's660MB
peak was dominated by reading tool files, not translation. Exact denied and
successful admission snapshots and both recipe versions are retained.

Failed Lean predecessors are EXCLUDED: missing generated Option discriminant;
local if/checked-sub/Option normalization; a map-membership binder; symbolic
Usize.max/Result bind syntax; and folding the source helper's let-bound request
list. Their compiler recovery sorryAx is retained in failed logs and absent
from every accepted declaration. The arithmetic API inspection is diagnostic,
not a proof/release target. No failed compiler object is selected.

`tools/s6-bump-reference-extract-20261026/check.py` reports PASS, auditing the
same Rust body, producer/consumer LLBC SHA pin without exporting LLBC, exact
normalization, receipts, resource limits, source/import identity and exclusions.
New evidence is source-only `focused-extractor-proof-packet-v1`; no binaries,
objects, LLBC or GOTO artifacts are committed.
