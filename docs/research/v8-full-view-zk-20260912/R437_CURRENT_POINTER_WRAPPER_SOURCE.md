# R437: actual pointer-wrapper source declarations

R437 exposes the previously opaque NonNull and PhantomData declarations used by the actual iterator constructor and fold. It retains their source type constraints and layouts, with unchanged native operation bodies. This is extraction and source-support evidence, not a Lean pointer/ABI or source-execution theorem, privacy proof or soundness proof.

## Capture and verification

Exact target: `R437PointerWrapperLayout.llbc`. Source revision at launch: `77857d6028d1b4016949aa14b19c17282e2cec0c`. SHA256: `bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c`. Charon exited0, `has_errors=false`, wall15.09 seconds, GNU peak RSS630,164 KiB, swaps0. Actual terminal cgroup peak495,079,424 bytes, zero swap and no OOM/high/max events. GNU and cgroup measures remain distinct, with no explanation inferred for their difference. Axioms: not applicable to diagnostic extraction; no Lean check was run for R437.

The command changes from R434 only by `core::ptr::non_null::NonNull`, `core::marker::PhantomData` includes and a fresh destination. Source and original toolchain hashes, selected features/flags, locked/offline release settings, caps, reservation checks and launch/collection receipts are retained. The job used MemoryHigh5 GiB, MemoryMax7 GiB, MemorySwapMax0, TasksMax128. Independent custody and lead source inspection passed. No verifier or tool source was changed, and no unchanged extraction or regression was rerun.

## Captured declarations

| Native declaration | Fields and constraints | Target layout |
| --- | --- | --- |
| 58: NonNull<QM31> | One `pointer` field: Pattern(shared raw pointer to QM31, NotNull) | size8, alignment8, offset0, transparent |
| 69: NonNull<[QM31]> | One `pointer` field: Pattern(shared raw pointer to slice of QM31, NotNull) | size16, alignment8, offset0, transparent |
| 59: PhantomData<&QM31> | Empty struct | size0, alignment1, no field offsets |

The recorded target is x86_64. Exact old/new rows and hashcons-expanded types are retained. The field constraint is not erased: pinned Rust source defines `pointer: crate::pattern_type!(*const T is !null)`, and pinned Charon translates this to `Pattern`/`NotNull`. Layout equality and transparent representation alone do not establish cast validity, address/provenance behavior or a valid source heap image.

Both constructor86 and fold70 compare equal across R434 and R437 after independently expanding capture-local hashcons/dedup and ignoring only source spans and statement IDs. No declaration remapping or extra ignored field was used. Complete rows, comparisons and check scripts remain saved.

## Existing backend boundary

The accompanying inventory reuses the exact pinned R430 source/support evidence, adding relevant Pattern source evidence where needed. The actual imported Charon-ML schema and JSON decoder preserve Pattern/NotNull. Aeneas pure-type lowering has no Pattern case and its wildcard rejects unsupported types; this source observation does not establish where a translation of this capture would fail. RawPtr in the Lean backend is a value wrapper, not an allocation/provenance model. Its scalar cast and unchecked slice-pointer APIs return `fail .undef`; a generic unchecked slice helper and spec contain `sorry`. The interpreter explicitly rejects raw-pointer dereference and aggregate raw pointers, and does not implement Offset or AddChecked in its scalar execution paths. Existing ordinary-reference, borrow and frame handling does not by itself close the raw-pointer source bridge. No unsupported definition or sorry was used in R432–R436.

## First remaining proposition

Represent the captured NotNull constraints and actual shared-slice input faithfully, then justify metadata, transparent-wrapper/raw-pointer casts, pointer arithmetic/distance and read validity, preserving provenance and legal empty/dangling cases. The existing R432 allocation bounds/nonzero results and R435 guard fragments are components; they are not a native primitive equivalence theorem. Bind native callback dispatch, mutable power restoration, frame, source loop invariant and every cleanup/error path before claiming whole-fold execution. Vec::extend and full callback/oracle chronology remain open.

Universal joint C1/H1/G compatibility including p0/p2 and adaptive/degenerate prefixes, full published-view simulation and shared-oracle losses, coherent original quotient extraction before beta and optimized-to-source acceptance remain unproved. Genuine 999,790 / 999,532 CU and every security parameter are preserved. No benchmark, deployment, merge, transaction or wallet operation occurred.
