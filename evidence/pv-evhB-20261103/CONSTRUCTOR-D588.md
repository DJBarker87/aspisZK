# D588 constructor and receiver association checkpoint

Resume `26bc9dfd6b`, branch `codex/pv-evhB-20261103`.
The four requested stages remain incomplete. In particular, neither unchanged
target equation is discharged. No reached native counterexample is claimed.

## Construction added at stage 1

`PV_EVHB_SourceLifetimes` separates source places from lifetime-indexed header
slots. An activation plus a field path names a source place. `newAt` mints
`State.next`, installs the constructor header and binds the destination place
to that lifetime; it increments the counter. `Fresh` bounds occupied-place
identities; `SlotsBefore` also bounds retained headers, so unreferenced old
slots do not justify reuse. `start` constructs an empty ghost source table at
entry. It is not a reset operation on an already-running interpretation.

Moves change the place environment, leaving the lifetime/header/world fixed.
Their source-valid use requires a distinct, vacant destination or prior source
drop. `receiverWorld` computes the selected registry from the place environment.
`callAt` computes both lifetime and header before invoking a source operation.
`tryReserveExactAt` uses that operation with `RawVecSource.tryReserveExact`.
No owner number or header is supplied as an argument of `tryReserveExactAt`.
All outcomes retain the exact returned world/events and the lifetime environment.

`originalSaltsNew` identifies the original `salts` local by activation and path
`[0]`. This is a constructed interpretation of the initial constructor/receiver
prefix, not an execution of the complete original entry or loop. The Nat
pointer argument still needs the actual type/layout and `without_provenance`
interpretation. A `dangling=true` boolean alone is not provenance evidence.

The new Lean module is **accepted and immutable**, receipt91232: exit0,
wall1.74s, peak2652680KiB, swap0, source32176754c608a927c6fd8601760fe9b068735d25.
All13 axiom prints are SUMMARY-BASED, subsets of propext/Quot.sound. This
acceptance credits the local laws described above, not native closure.
Attempt91231 failed before the changed-source repair of move conditional
elimination and constructor-call let syntax. Its sorryAx summary earns no credit.

## Source evidence

`lifetime-source-D588.json` pins six exact Rust 1.94.1 source spans and three
original adopted application bodies. The chain is:

1. Original `derive_private_salts`: `let mut salts=Vec::new()` followed by
   `salts.try_reserve_exact(FIBRE_COUNT)` on that same local.
2. `Vec::new`: `RawVec::new`, initialized length zero.
3. `RawVec::new`: `new_in(Global)`.
4. `RawVec::new_in`: the same T's layout/alignment, then `RawVecInner::new_in`.
5. `RawVecInner::new_in`: `without_provenance(align.as_nonzero())`, zero cap.
6. Reserve receiver projections: `self.buf`, then `self.inner`, with the
   same length/additional and the same T's layout.

This is labelled **partial own-1 structural binding**. It is not a compiler
preservation proof. V370 remains. L3 physical-frame facts are not prerequisites
of these source-level effects or the L1/diagnostic projections (l3-2).

`std-inputs-D588.json` records seven additional installed 1.94.1 source inputs,
their hashes/sizes/host paths and exact deployed-version `rustc -vV` parity.
These are read-only inputs for stage 2; Global/System-to-V183 correspondence
is not claimed. No native program, Kani, extraction or build was executed by
the collection. The source package's relation to machine code remains V370.

Stage-2 inspection notes (not proof credit): `Global` now dispatches through
`const_eval_select` to its runtime helpers. Allocation size zero returns a
dangling empty slice; positive size maps null to `AllocError`. Positive-size
same-alignment growth uses `realloc`; changed alignment uses allocate, copy,
then deallocate, and denial returns before copy/deallocate. RawVec's
`finish_grow` preserves T's alignment, but that source invariant must be proved
at the interpretation boundary rather than deleting the generic Global branch.

On the adopted x86_64 Linux target, `System` uses `MIN_ALIGN=16`. Low-alignment
alloc/realloc paths call libc malloc/realloc; larger alignment selects aligned
allocation or `realloc_fallback`. The latter allocates first, copies
`min(old_size,new_size)` and frees the old block only on success. Arbitrary A
therefore needs those branches even if `[u8;32]` takes the simple path. Global
allocator shim selection (`__rust_*` versus `__rdl_*`), libc/world answers and
all nonreturning effects still require association. Absence of a project-local
`#[global_allocator]` alone would not establish the dependency/link selection.

V183's ordered history counts reserve allocation/growth macro requests. It
does not by itself enumerate all lower-level allocation/copy/free/OS effects
inside a System fallback. A returning projection may aggregate the former;
the native interpreter must retain the latter in its world and event prefix.
The existing modeled `memoryAfter` equality is not proof of actual libc heap
adequacy or physical residue observations.

## Exact remaining stage-1 obligation

For **every** reserve/push receiver reached from the ORIGINAL extracted entry,
construct the source state by executing that entry's constructor, move,
argument, Result-payload, return-payload and drop transitions. Let `p` be the
receiver's actual source lvalue in its actual activation. Derive a minted
lifetime `id` and header `h` such that:

```
s.places p = some id
lookup s.world id = some h
h interprets that source receiver's ptr, STORED cap, len and T layout
receiverWorld s p = some (OwnerRegistry.project id s.world)
```

The state, activation, `p`, layout interpretation and original-prefix
association are to be constructed, not hypotheses added to the endpoint or a
compatibility record. This displayed statement is a specification, not an
elaborated theorem: there is still no complete original-prefix interpreter
constructing `s`. The current module supplies the constructor/move/receiver
mechanism and its local laws. It does not install all those source transitions.

Original loop coverage includes `Ok(salts)` into `result`, extraction into the
step argument, `salts.push(salt)`, return `Ok(salts)`, the next iteration, and
`PrivateSalts::new`'s `Self(values)` move. Allocation/semantic failure and
nonreturn paths must retain their drop/diagnostic prefixes and cannot reuse a
moved-from or consumed place. Entry-to-first-constructor reachability and all
earlier constructors also need the same ghost-state threading.

After this, bind actual Global/System operations and world answers to V183;
derive `reached_reserve_header_delivery`; then derive the exact constructed
v263 runtime/growth instance in `SHARED-VEC-D580.md`, in that order. Existing
modeled header-delivery theorems alone do not discharge those steps.

No T field, target binder/domain, source deployment, endpoint row, resource
failure branch, rdea-1/rdea-2/V400, V370/L3 or V183 K-3 status is changed.
