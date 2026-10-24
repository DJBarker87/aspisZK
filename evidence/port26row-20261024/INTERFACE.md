# Port26ROW concrete equality and boundary

Candidate remains UNMERGED/UNADOPTED. Source revision context and independently
hashed proof inputs appear in every receipt. No shipped source, installed
interface, protocol, feature, trust field or security contract changed.

## Complete before/after statements

Before, accepted Port23PUSH.push_complete (unchanged):

```lean
∀ (ι : Port23PUSH.ArrayIntoIter) (b : verifier.BatchedWeights)
  (index : Usize) (power : field.QM31) (basis : U32),
verifier.BatchedWeights.push ι b index power basis =
  do let row ← Vec.index (SliceIndexUsizeSlice (Array U64 4)) b.raw index
     let updated ← verifier.update_residue_row ι row power basis
       ((b.terms &&& 3) = 3)
     ok {b with raw := b.raw.set index updated}
```

After, new accepted Port26ROW.row_complete:

```lean
∀ (row : Array U64 4) (power : field.QM31) (basis : U32) (flush : Bool),
verifier.update_residue_row Port25ARRAY.concrete row power basis flush =
  S7Kani2OwnedRow.residue_owned row (Port26ROW.toK power) basis flush
```

New accepted Port26ROW.push_complete:

```lean
∀ (b : verifier.BatchedWeights) (index : Usize)
  (power : field.QM31) (basis : U32),
verifier.BatchedWeights.push Port25ARRAY.concrete b index power basis =
  do let out ← S7Kani2OwnedPush.push_owned
       (Port26ROW.toBW b) index (Port26ROW.toK power) basis
     ok (Port26ROW.fromBW out)
```

The numeric literals above abbreviate the exact typed `#usize` constants; full
checked statements, carriers, bodies, dependencies and axioms are printed in
lean-008/lean.log. These are new specialized source-content theorems, not removal
of the installed Port3 native equality premise. They impose no run/equality,
safe-domain, index-bound, canonicality, power-word, basis or term assumption.
The concrete constant is a defined composition, not a hypothesis asserting
success. `toK` copies all four U32 words into two pairs; toBW/fromBW copy all raw
rows and terms. `carrier_roundtrip` proves exact inverse on the source carrier.

## Actual body and full Results

Port26ROW_Steps accepts the retained owned_four, row_four, add_unroll and
range_next directly from valid proofs, without importing failed Port25 audit
objects. fold_body_complete explicitly destructures next's Result/tuple; both
none and some branches retain the actual deferred writeback closure.

Port26ROW_Add normalizes each actual add body and all four loop tails, including
the stopped range. Checked products and raw adds stay in their source order.
Port26ROW_Fold normalizes each actual iterator body and all five loop states,
then proves complete readback through the original iterator, four nested slice
writes and Array.from_slice. Original length-four content guarantees the normal
readback; the generic existing wrapper's fallback was not altered.

Existing Port25.fold_total/fold_eq applies to every U64. scalar_all_results
rewrites owned per-lane add/fold into checked add followed by pure total finish.
owned_four uses bind associativity to put all checked adds first; a total pure
finish can cross subsequent checked computations without changing their fail
or div outcome. No native effect commutation is inferred. Source row_complete
then equates the two concrete normal forms, not an abstract wrapper premise.

owned_push_complete normalizes the actual owned Vec getter/setter for all
indices. Combined with the unchanged Port23 full mutable frame and row_complete,
this proves the complete BW Result equality. Entire Vec.set and terms remain;
bad indices fail before the row body. Overflow is still an actual fail outcome,
not ruled out by a new invariant. No partial native memory/panic behavior is
represented by equality of these pure Results.

## Literal collection call, D157 and P6 scope

source-assessment.json records and expands inherited LLBC caller def3's exact
call to def14: `core::array::<IntoIterator for &mut [T; N]>::into_iter`,
T=U64, N=4, moved mutable array borrow local35 to iterator local34. The native
ABI takes `&mut [U64;4]` and returns `IterMut<U64>`. The functional translation
also needs the deferred borrow-return continuation. The actual caller passes
the completed iterator transformer to that continuation:

```lean
ArrayIntoIter := Array U64 4 →
  Result (IterMut U64 × ((IterMut U64 → IterMut U64) → Array U64 4))
```

Inherited pinned source array/mod.rs:376-378 implements exactly
`fn into_iter(self) -> IterMut<'a,T> { self.iter_mut() }`; slice/mod.rs:1061-1063
calls IterMut::new. This is the literal delegation associated with the new
content composition. The association is tied to THIS call/borrow/type/length,
not a favorable arbitrary array-success interpretation.

Port25ARRAY.concrete derives that composition by existing Array.to_slice_mut,
Slice.iter_mut and Array.from_slice wrappers. Its transformer is applied to the
original iterator before slice and array readback. D157 LOG.md:8389ff permits
pure called collection/iterator content semantics, and explicitly excludes
new policies for unsafe internals, interior mutability, panic/allocator failure,
concurrency and I/O. Thus this composition remains within the EXISTING approved
pure collection-content boundary; zero TrustedStd fields or trust assumptions
are added. Mutable native pointer/provenance/order behavior is not established
by that pure composition. The native source's IterMut::new uses unsafe pointer
construction; it is not independently verified or newly trusted here.

The generated raw external template takes `IterMut → Array` where the caller
requires `(IterMut → IterMut) → Array`. It was never accepted/imported. Its
wrong argument is an unused generated stub, not evidence requiring verification
of all Aeneas or adoption of a backend change. Exact parameter threading and
otherwise unchanged emitted bodies pass Port23 promote --check. Source-level
call association and content-instance equality are now explicit. Execution
association under the existing P6 collection boundary, with sufficient ordered
native effects, remains the specific native consumer obligation. Neither a
new backend registration nor a universal compiler-correctness gate is claimed.

## Effect producer and release frontier

Actual source fixed order (in the inherited selected source/LLBC): terms mask;
Vec mutable index; row loop j=0..3 with row read, power read, two widening casts,
product, checked raw add and row update; optional mutable array iterator;
next/mask/shift/add for each of four limbs, stopped next, deferred writebacks;
outer Vec setter. Rejection at the Vec index or an arithmetic/collection fault
cuts off that actual suffix. This is a source inventory, not an ordered native
RO/fault/panic-prefix theorem. The pure owned normal form reorders total folds;
it cannot supply an effect trace merely because its outputs agree.

No source effect producer or NoHash theorem is claimed. Need the actual fixed
primitive interpretation, ordered rejected prefixes, and association with the
source/native execution at this local call graph. NoHash cannot be inferred
from Result equality, NoDigest or lack of an explicit hash in these bodies.
Then compose the concrete native frame consumer, op6's other four_dots,
geometry/line/circle/accumulator children, trace/observer and release join.
No new allocation prerequisite is introduced for this nonallocating function.
Port17 release None invariant retains only its proved actual None-start scope;
no arbitrary Some-to-None retargeting. Both deployed targets not established.

## Validation and failures

Eight slots used, no reset of prior charges. 001 Steps,003 Add,006 Fold,007 Row,
008 Audit exit0; 002 Add,004 Fold,005 Fold exit1. Failed snapshots/logs retained.
002 needed final tuple reduction at stopped range; 004 required rewriting the
actual body Result after symbolic unroll and removing readback tuple lets;
005 dsimp made no progress on that tuple. An explicit typed change in 006
closed readback. No mathematical counterexample and no resource failure.
Failed modules have recovery sorryAx in logs only; none are imported/accepted.

Final Audit imports accepted Row and exercises invalid-index failure. It prints
all new definitions/theorem statements, actual/owned carriers, scalar/collection
wrappers, and full #print axioms. Standard axioms only. New evidence contains
exact command/target/exit/wall/RSS/swap/revision, source/dependency/object/tool/
sysroot hashes before/go/after. Source snapshots, including untracked inputs,
identify what compiled; HEAD is context, not a false assertion that dirty proof
text existed in that commit. Fresh assessment verifies all eight exits and
current accepted module/direct-dependency identities, including reused Port25
Std/Lane source/object/dependencies. Warm reuse is not a coherent release replay.
Early Port23 integrity limitations remain unchanged, with no historical repair.

Local only: existing atomic shared lock, j1/M4400 and aggregate8GiB guard; no
host launches, cold builds, cap raises, full manifest, Rust, Kani, extraction,
backend or ELF gate. All swap0; maximum RSS2,255,962,112 bytes. Known global
prior339 plus this job8 =347/368 (other concurrent charges not assessed).
