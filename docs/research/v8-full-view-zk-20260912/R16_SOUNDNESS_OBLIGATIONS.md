# R16 soundness preservation obligations

## Retained arithmetic foundations replayed in full runtime — 2026-09-21

Base revision `c479081a` plus this changeset. The source caller imports the
full cached runtime, while earlier arithmetic proofs used authenticated
declaration projections. Importing both copies into one environment is not
an arithmetic correspondence proof. New stage_full_runtime.py authenticates
the original runtime blocks using the existing checker, omits their 12/5/5
duplicate declarations, imports Aeneas.Std, and REPLAYS the unchanged theorem
statements/bodies of UnsignedCoreSlice, UnsignedCM31Cross and UnsignedReducerOps.
The retained field declarations in UnsignedCM31Cross are not removed. Original
tracked projection files/caches remain unchanged. The new proof cache excludes
the old declaration-projection workspace from LEAN_PATH.

All three focused leaves compile against the actual full-runtime constants.
The existing checker verifies seven runtime source pins and rejects three
mutations per mode; the staging generator verifies theorem-block byte equality,
records original/staged hashes and supports read-only --check. This advances
the foundational runtime bridge, NOT the complete new field namespace or
the source mask loops.

There is also an operational distinction beyond namespace/type ownership:
the new source extraction explicitly uses wrapping operations where parts of
the older retained arithmetic projection use checked operations. New
FullRuntimeWrapping.lean proves actual-runtime checked/wrapping agreement for
U64 addition/multiplication under their explicit no-overflow bounds and U32
subtraction under y≤x. A compiled underflow negative regression proves they
cannot be equated unconditionally. These are arithmetic preconditions to be
discharged by the caller, not new cryptographic/hiding assumptions.

Cached Lean 4.32.0 -j1 -M3200; sequential scopes with MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, TasksMax=64. Preflight showed only init.scope.
New full-runtime import environment justified the focused replays; there was
no old full-manifest rerun or memory-failed target/cap increase. Units below
have prefix aspis-r17-full-runtime-; targets are under AspisV8R17.

| Exact target / unit suffix | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| UnsignedCoreSlice.lean / core-r1 | 0 | 1.11 | 2559044 | 0 |
| UnsignedCM31Cross.lean / cross-r1 | 0 | 1.23 | 2573844 | 0 |
| UnsignedReducerOps.lean / reducer-r1 | 0 | 1.08 | 2561860 | 0 |
| FullRuntimeWrapping.lean / wrapping-r1 | 1 | 1.08 | 2553384 | 0 |
| FullRuntimeWrapping.lean / wrapping-r2 | 0 | 1.24 | 2568520 | 0 |

Wrapping r1 attempted definitional reduction through irreducible runtime size
constants; r2 uses their explicit size equations. R1's sorryAx diagnostics
were not accepted. R2 has three harmless unused-simp-argument warnings.
Final axioms: four core theorems use propext; four cross theorems use
propext/Quot.sound; reducer-operation theorems use propext except and_value
also uses Quot.sound; all four wrapping/agreement-negative theorems use
`[propext, Classical.choice, Quot.sound]`. No new assumptions or sorryAx.

Final cache: `/home/dombarker/project-offloads/aspis-r17-mask-extract.aRLUCU/full-runtime-r2`.
Original inputs are in full-runtime-inputs-r1; compile workspace was
full-runtime-r1. Creation/--check pass; compiled sources are byte-compared
before olean reuse in r2. Original/staged SHA256s are in full-runtime-stage.json.
Staged hashes:

- UnsignedCoreSlice: 570ed7545ef492c17ac660764403447580e492e66cff5650c1df09ab6fe33183;
- UnsignedCM31Cross: 377dd74616466e2e3e9f44276940214910f7da048a09ea3f36f8c585b0c4e6db;
- UnsignedReducerOps: 5f222d185d9f260b9cb53e29f55e899df67fb34dfc885190781addcf7c50d915;
- FullRuntimeWrapping: 931b014981e7fd221a78f02414926420536ffc2a11d707c3322e1099ae2e22fc.

The runner additionally pins WrappingOps/Add, Mul and Sub respectively to
6b20fc30c237b8bfac99f9cd1e45f8150edcaabe4c62fdca5b0ceeb3a4a9b1a4,
4d6f81c964cfa9b3b6808bc6d2703d3f2dbde5c70ce3ae76541905304802beb8,
a07d2e801092fe35e9e0fd376a9723a2e1486467ff08769faae7644f55ce898e.
These source hashes were checked on the compile host. The added runner pin
guards were syntax-checked; no unchanged theorem replay was needed for them.

First remaining arithmetic proposition: discharge these bounds and the
wrapping-shift correspondence in the actual new reduce_u64/M31/CM31/QM31
bodies, retaining modular/canonical results and connecting the fresh field
types. Then use those results for reverse coin construction and accumulation.
No source mask-loop or global privacy/soundness obligation was declared closed
by this foundation replay. Production, Rust candidate, source pins and all
negative regressions are preserved.

## Actual buffer-clearing loop: termination and stale-state erasure — 2026-09-21

Base revision `5e21b4c4` plus this changeset. New WorkspaceZero.lean imports
the actual import-only-staged caller and proves its output-clearing loop,
not a replacement trace. `workspace_zero_loop` uses well-founded induction
on `1024 - j.val`, exact Array.update_spec and wrapping-add semantics. For
any start j ≤ 1024 with the preceding prefix zero, it proves a successful
return and all 1024 coordinates zero. `workspace_zero_from_start` discharges
the prefix/start premises for j=0. `workspace_zero_independent` then proves
the clearing loop's complete Result is identical for ANY two initial buffers.
There is no canonical-field, termination, no-overflow or success premise on
the initial buffer: it may contain arbitrary QM31 word values.

This closes the candidate's stale-output-buffer initialization sub-obligation,
not the later coin construction, accumulation, arithmetic correspondence,
complete caller termination, global witness privacy or protocol integration.
In particular it says nothing yet about the scratch coin buffer's overwrite.

The proof first establishes symbolically that j<1024 makes j+1 fit usize,
using the runtime's 32/64-bit platform split; it does not evaluate a 1024-step
recurrence. The array argument stays symbolic throughout. All three final
theorems audit to `[propext, Classical.choice, Quot.sound]` only.

Target: AspisR17MaskSource/WorkspaceZero.lean in retained host
`aspis-r17-mask-extract.aRLUCU/workspace-staged-r1`. Cached Lean 4.32.0,
-j1 -M3200; sequential scopes MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0,
TasksMax=64. Preflight showed only init.scope. No dependency rebuild or
unchanged full replay. Unit prefix: aspis-r17-workspace-zero-.

| Attempt | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| r1 | 1 | 1.17 | 2562324 | 0 |
| r2 | 1 | 1.33 | 2561588 | 0 |
| r3, loop/from-start theorems | 0 | 1.24 | 2571700 | 0 |
| r4, buffer-independence corollary | 0 | 1.35 | 2573152 | 0 |

R1 used reserved identifier `prefix` and an insufficient generic scalar tactic
for the usize-size bound. R2 corrected the identifier but still needed the
runtime's irreducible Usize.size/numBits wrappers unfolded and the explicit
index bound in the set-at-current-position case. R3 fixes these; r4 adds
array extensionality to show output independence. Failed attempts' sorryAx
diagnostics were not accepted. Final r4 has two harmless unnecessary-simpa
warnings and no errors. No memory limit changed.

Final leaf SHA256:
`d6f45e8444817caf080238835ab4e91bc11234352f44c307accdc4640eb2e44d`.
stage_workspace.py now copies/checks the leaf alongside the unchanged raw-pin
validated caller; --check passes. The focused runner allowlists WorkspaceZero.
Production, candidate Rust, old implementation and negative controls are
unchanged, so no unrelated Rust regression was rerun.

Next source propositions: prove the reverse-round coin writes and subsequent
mixing accumulation on the actual extracted buffers, with all field operations
justified by the full-runtime arithmetic bridge. Then close universal
equivalence and arrange staged-profile buffer acquisition/failure handling.
The source-extraction/library trust boundary and full transcript/security
obligations remain explicit and open.

## Caller-buffer mask candidate; direct extraction compiles — 2026-09-21

Base revision `71a94b77` plus this changeset. Added a separate research source
`tools/r17_mask_workspace.rs`; the pinned original r17_structured_g.rs and
field.rs are unchanged. This candidate addresses the demonstrated allocator
model gap by taking caller-owned `[QM31;271]` scratch and `[QM31;1024]` output
buffers, computing the same reverse-round coin weights, then accumulating
each mixing power directly. It uses bounded index loops rather than Vec,
map/collect or mutable zip. It overwrites the buffers, does not draw new masks,
and does not change commitment, oracle, pad or challenge chronology.

This is not yet selected by the staged protocol or production. Its pure
field-operation order interleaves power generation and accumulation where
the original materializes a full row first; universal equivalence/totality
must be proved, not inferred from the finite controls. Caller buffer
acquisition and failure/publication behavior remain separate. The function
does not allocate large local arrays, but callers must supply appropriate
storage: the host probe's stack placement is NOT an SBF deployment plan.

Optimized host controls compare all 1024 coordinates on 16 canonical point
arrays, including all-zero, all-one and all limbs P-1. Buffers are reused
without cleaning. While the candidate runs, a diagnostic allocator denies
ALL allocation attempts; every candidate call returned and the attempt
counter stayed zero. This is finite actual-source evidence, not a universal
no-allocation theorem, field-equivalence proof or global privacy claim. The
original allocation/abort regressions remain intact.

New extraction-only workspace_lib.rs wires the unchanged original module,
field and new candidate into the same dependency-free crate. Charon targets
`crate::r17_mask_workspace::mask_weights_into` with the retained pinned binary,
MIR built, preset aeneas, offline/locked/release/lib/no-default-features, one
Cargo job. Aeneas uses the retained pinned binary/flags. Its raw output has
only Types/Funs, no external template, no map/zip warnings, no Vec/allocator
references and no axiom/sorry declaration. This is source extraction of the
new implementation, not replacement of old source by a synthetic trace.

`stage_workspace.py` authenticates both raw generated files and narrows ONLY
imports for the cached Lean runtime. No declaration, loop, field operation,
borrow signature or function body is rewritten; no IteratorCompat model is
imported. The full extracted caller compiles with five loop definitions.
AuditWorkspace prints only `[propext, Classical.choice, Quot.sound]` for all
five loops and the caller. This audits executable definitions, not correctness
or termination. The generator's --check passes against the compiled source.

Focused scopes: MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64;
preflight showed only init.scope. Rust is cached nightly-2026-06-01, rustc
1.98.0-nightly (14210df0e), -O for the comparison/denial probe. Lean is cached
4.32.0 -j1 -M3200. All jobs were sequential, no cold dependencies or unchanged
full suite. Unit names below have prefix aspis-r17-.

| Exact target / unit suffix | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| workspace_probe.rs optimized build / workspace-r1 | 0 | 0.40 | 145084 | 0 |
| workspace-probe, 16 cases / workspace-r1 | 0 | 0.14 | 2112 | 0 |
| mask_weights_into to LLBC / workspace-extract-r1 | 0 | 0.96 | 213804 | 0 |
| LLBC to raw Lean / workspace-translate-r2 | 0 | 0.89 | 103488 | 0 |
| AspisR17MaskSource/Types.lean / workspace-types-r1 | 0 | 0.89 | 2114448 | 0 |
| AspisR17MaskSource/Funs.lean / workspace-funs-r1 | 0 | 1.41 | 2579412 | 0 |
| AspisR17MaskSource/AuditWorkspace.lean / workspace-audit-r1 | 0 | 1.06 | 2551032 | 0 |

Translation launch r1 had no copied translate.sh and therefore never ran the
translator (bash missing-file exit 127; enclosing diagnostic shell exit 1).
After copying the retained script, r2 translated the SAME intact LLBC once.
No source/tool pin was waived and no memory-failed job was retried.

Host artifacts are under `aspis-r17-mask-extract.aRLUCU`,
in `/home/dombarker/project-offloads`: workspace-r1, workspace-extract-r1,
workspace-lean-r1 and workspace-staged-r1. SHA256s:

- candidate Rust: 9ba932ba6ffabd31781b32dbc1f4a0f28020639bd0798aa3d8a7e1ec3be4e5b8;
- optimized probe: 2beaf92cb57ddf960ed0419de99b3af26bdf1a6bb9e87194695bffeadb12fc57;
- LLBC: 09a190991bdb71ad95eb2d348fbd4cbb538aeef81ee6504a01031f4d13f5cd2b;
- raw Funs: 951d864bcc7238e6e61eaed240632fe7eb90e7d132ab63b97d75b9acef095b8f;
- raw Types: a29d7a2e4067ece0ff887ebb0eff3a3e49f28aa6436cdba289bf9b3c07c5cc33;
- compiled Funs: 5f2d6de84fdbdf05f4f6f9cede9409a4781d37eac21425b8c5f5b6a3819c33c9;
- compiled Types: e212e91df0604408ac89fef369244cacaa6d6635d97bd855f02d0e5e239eaf06;
- audit: 69638321e457e5220900a02d74d767ce58cdbf1cf402d5ac1a63fba69a3d0ca3.

First remaining proposition: for every canonical point and every initial
scratch/output buffer, the direct extracted index loops terminate, overwrite
all coordinates and return exactly the retained mask functional. This needs
the full-runtime arithmetic correspondence and loop bounds/invariants, not
another finite comparison. Source-profile integration must then arrange
buffer acquisition before using the candidate, retaining a justified visible
failure law. Earlier oracle/commitment/retry/publication and soundness gates
are unchanged and still open. No production switch or full repair claim.

## Actual-source allocation-abort regression — 2026-09-21

Base revision `09310660` plus this changeset. This turn adds focused Rust
diagnostics, not a new Lean theorem or an attack-frequency search. The
unchanged pinned field.rs and r17_structured_g.rs are compiled with a
diagnostic global allocator and extraction-only module wiring. The allocator
records size/alignment/kind in fixed atomic storage, and can deny a selected
allocation by returning null. Input parsing/logging occurs outside the armed
region. Each denial runs in a separate subprocess with core dumps disabled;
no wallet, production process, shared allocator setting or production source
is touched.

New tools are allocation_probe.rs, check_allocation.py and run_allocation.sh
under tools/r17-mask-extraction. Source pins remain 5795495e... (field) and
147be74e... (research module), checked in full before compilation. The runner
uses explicit cached nightly-2026-06-01 rustc, edition 2021 and -O; version
1.98.0-nightly (14210df0e 2026-05-31). Expected work was one dependency-free
optimized compilation and eight bounded diagnostic executions, not dense
field elimination. Preflight showed no other task scope running.

Scope aspis-r17-allocation-r2: MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64. An initial r1 launcher stopped at exit 127 before
compilation because noninteractive PATH lacked rustc; the runner was changed
to its absolute cached path and r2 used a fresh directory. No failed source
test or memory-pressure job was retried unchanged.

| Target | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Optimized allocation_probe.rs compilation | 0 | 0.38 | 145584 | 0 |
| check_allocation.py, eight child cases | 0 | 4.38 | 13728 | 0 |

Verified finite observations in this instrumented optimized binary:

- mixing_row(0) and mixing_row(1) each returned 1024 field elements and each
  made one 16384-byte, alignment-4 allocation.
- mask_weights for two explicit canonical point arrays each returned 1024
  elements and each made 272 such allocations; their recorded allocation
  traces match. This is a two-input control, NOT a universal independence law.
- denying mixing_row's first allocation, or mask_weights allocations 1, 2,
  or 272, caused SIGABRT (subprocess returncode -6) with the 16384-byte OOM
  diagnostic and no returned result. The harness requires all four aborts.

The allocator is a test instrument, not the production allocator, and Rust
may optimize allocations. Counts are evidence for this pinned instrumented
binary, not a language-level allocation guarantee or a production release
test. No runtime assertion proves global privacy or a malicious-prover bound.

Host artifacts: `aspis-r17-mask-extract.aRLUCU/allocation-r2` under the retained
project-offloads root. SHA256s:

- allocation_probe.rs: 6ba37bb64cf7ab6f4716771fd357eb4d9323f994f14c09ff5d652a541f75e19c;
- optimized binary: 34f4d889be0160a45afd54b136dee0e88b9b3ec45159137878c4bb75d7382f4c;
- results.json: f91c07ea8d7f02f5aa71be48a0beb8d2933545c21137f6602f573893cecd6585.

Additional source inspection: cached alloc/src/vec/mod.rs, SHA256
a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f,
extend_trusted at lines 4056ff reserves the size-hint amount, then uses
for_each with ptr::write and SetLenOnDrop. Thus capacity, allocation abort,
traversal order and partial-state destruction are distinct source obligations;
the cached collector's final Usize length check does not establish them.

Precise remaining obstruction: the current Lean Result model has no allocator
state or process-abort observation corresponding to these Rust executions.
An unconditional Rust-to-Result claim including all allocation environments
would therefore be unjustified. Either the source/environment correspondence
must explicitly represent aborts and their publication consequences, or the
repair must establish a justified allocation discipline and its observable
failure law. Merely assuming allocation succeeds, or extrapolating independence
from the two successful traces, does not close the full-transcript goal.
This is not a newly demonstrated privacy or soundness attack. Ordinary
source mask-loop invariants and the field-projection connection also remain
open; earlier compiled statements and negative regressions are preserved.

## Collector Result equivalence, instantiated in mixing_row — 2026-09-21

Base revision `045e2f40` plus this changeset. New CollectorLaws.lean proves
UNCONDITIONALLY that observing the value component of collectListState equals
the cached runtime's iterToList. The proof uses partial-fixpoint induction in
both directions with the flat divergence order; it does not assume finite
termination, supply fuel, or restrict the theorem to successful runs.
collectState_observe lifts this through vector construction and the exact
cached `length ≤ Usize.max` check. Values, failure constructors and divergence
are preserved. Final iterator state remains available in the richer model.

AuditCaller.actual_mixing_row_collect instantiates this result in the actual
staged mixing_row, leaving its bounds assertion, wrapping index addition,
scalar construction, captured closure, and map iterator instance intact.
This closes the candidate collector's observable-Result correspondence to the
CACHED MODEL; it does not prove that the cached model captures Rust allocator
failures, Vec specialization, or the whole source pipeline.

Exact focused commands use run_iterator.sh and the retained cache, Lean
4.32.0 -j1 -M3200; each scope has MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64. Units below use the aspis-r17- prefix. No
unchanged full replay, memory-pressure failure, or raised-cap retry occurred.

| Exact target / unit suffix | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| CollectorLaws.lean, signature probe / collector-probe-r1 | 0 | 1.07 | 2553068 | 0 |
| CollectorLaws.lean / collector-r1 | 1 | 1.25 | 2561868 | 0 |
| CollectorLaws.lean / collector-r2 | 1 | 1.20 | 2561420 | 0 |
| CollectorLaws.lean, list theorem / collector-r3 | 0 | 1.16 | 2573120 | 0 |
| CollectorLaws.lean, vector theorem added / collector-r4 | 0 | 1.25 | 2574356 | 0 |
| CollectorLaws.lean, unused simp arguments removed / collector-r5 | 0 | 1.24 | 2573248 | 0 |
| AuditCaller.lean, actual source instantiation / collector-source-r1 | 0 | 1.11 | 2569280 | 0 |

All targets reside under AspisR17MaskSource. The initial probe only inspected
Lean's generated induction/equation signatures. Attempts r1/r2 failed to infer
the nested admissibility predicate/function types; r3 supplies those types
explicitly. Their error-generated sorryAx outputs were NOT accepted. Final
collectListState_observe, collectState_observe and actual_mixing_row_collect
audits use only `[propext, Classical.choice, Quot.sound]`. The dependent audit
also checks the generated mixing_row/four loops/mask_weights; no new axioms.
The pre-existing harmless actual_map_step unused-simp warning remains.

Generator staging and --check both pass for final host artifact directory
`/home/dombarker/project-offloads/aspis-r17-mask-extract.aRLUCU/iterator-r3`.
Compiled sources were byte-compared before cache reuse from iterator-r2;
unchanged Funs, Types and iterator dependencies were not rebuilt. Final hashes:

- CollectorLaws.lean: 7f8e10953754f2333759e62820224cf6df2a798bc8d310e1b28518ad42bb4ffc;
- AuditCaller.lean: b7ad7d5920e546d27f5f4db9070de40a5b3ab3e29336160758d1131a7422fffd.

### Concrete standard-library dispatch inspection (not a Lean theorem)

Read the cached nightly-2026-06-01 Rust sources. For this caller's
Zip<IterMut<QM31>, vec::IntoIter<QM31>>, the NoCoerce specialization includes
zip_impl_general_defaults, whose next calls the two next operations in order.
IntoIter explicitly does NOT implement TrustedRandomAccess (without
NoCoerce); its source explains why. Thus the separate indexed Zip::next
specialization must not be substituted for this call. This narrows the
remaining correspondence problem; it is source inspection, not a certified
rustc dispatch proof or a blanket theorem about all zip iterators.

Collection is different: usize is TrustedStep, Range<usize> is TrustedLen,
and Map preserves TrustedLen. Vec's nested TrustedLen collector allocates
with the size-hint upper bound, then calls spec_extend/extend_trusted.
The abstract cached list collector does not by itself justify that allocation
and specialized traversal path. Full-transcript failure/publication behavior
must not silently assume successful allocation merely because the fixed
output length is 1024.

Additional inspected source SHA256s (paths relative to rust/library):

- alloc/src/vec/spec_from_iter.rs: 393d1f28cfc8d28d80e142cef6b612aae9b484160969cfa0c9f97bb894534807;
- alloc/src/vec/spec_from_iter_nested.rs: f3c1a06f43734a65e102b6a107e2fd5adadd7d94d9a226d6ffe1610d1e7e1466;
- alloc/src/vec/spec_extend.rs: a0816ad0f39b947889771bf06930bf8e0c4ce794846d83863349697ec7c415ec;
- alloc/src/vec/into_iter.rs: 7fef46007c1e9e2fbbcc1967f824f9eb8031b18d46984be4903325fa8bd21564;
- core/src/iter/adapters/zip.rs: 29d8c1c971d934d6a2f11c71516717ae39289d7a1b09e08e42238fb75188fb89;
- core/src/slice/iter.rs: 83205f82241154964b1aecef87913ec92ce8c0b99285337c04e37840594f9251;
- core/src/iter/range.rs: df884a169ec674a8d97312096d195b68f0d1761f4ef282a85450f02b1e4ca079.

First remaining source proposition: the concrete TrustedLen vector collection
and mutable slice/owned-vector operations refine the cached operational model,
with their allocation/failure observations accounted for. The mask-loop
invariants and full-runtime field/arithmetic-projection connection remain
unproved. No full privacy/soundness claim follows; joint views, oracle/seed
expansion, retries/publication and explicit security losses remain open.
Production and negative regressions remain untouched.

## Staged full mask caller compiles with explicit iterator models — 2026-09-21

Base revision `15bf4615` plus this changeset. The prior interrupted turn wrote
the candidate adapter; this turn compiled and scrutinized it. Production
Rust, the raw generated artifacts and all negative regressions are unchanged.

New `tools/r17-mask-extraction/IteratorCompat.lean` supplies explicit
borrow-aware FnOnce/FnMut records, Map construction/next, state-retaining
collection, and mutable-slice/owned-vector zip construction/next. Map.next
APPLIES the generated closure's returned write-back; collection retains the
final iterator state instead of fabricating a value for its ignored return.
Mutable zip advances its second iterator only after the first yields Some,
and writes a replacement FIRST item back into the current first iterator.
Its ordinary Iterator dictionary has a forward-only next; the actual mutable
zip path explicitly calls the full next with its backward function.

`stage_iterator.py` pins the complete raw Types/Funs and records 11 exact,
count-checked replacements in iterator-stage.json: imports, enriched closure
trait interfaces, map/collect dispatch and mutable zip dispatch. Field
operation bodies, arithmetic/array instructions and the four generated loop
bodies' remaining instructions are not rewritten. This is an EXPLICIT
compatibility-model stage, NOT an authenticated compiler transformation or
an end-to-end Rust refinement. In particular collectState is a candidate
state-retaining version of the cached Vec collector; equivalence and concrete
Rust iterator specialization/allocation behavior still require justification.
No FunsExternal template was imported and no external axiom was added.

Focused results, cached Lean 4.32.0 -j1 -M3200, sequential scopes with
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64. The host had only
init.scope at preflight. Time is elaboration/kernel checking, not arithmetic
generation or a dependency rebuild. Prefix of units is aspis-r17-.

| Exact target / unit suffix | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| AspisR17MaskSource/IteratorCompat.lean / iterator-r1 | 0 | 1.21 | 2574600 | 0 |
| AspisR17MaskSource/Funs.lean / mask-funs-r1 | 0 | 1.44 | 2589192 | 0 |
| AspisR17MaskSource/AuditCaller.lean / mask-audit-r1 | 0 | 1.08 | 2560540 | 0 |
| AspisR17MaskSource/IteratorLaws.lean / iterator-laws-r1 | 0 | 1.34 | 2570808 | 0 |
| AspisR17MaskSource/AuditCaller.lean / mask-audit-r2 | 1 | 1.10 | 2556232 | 0 |
| AspisR17MaskSource/IteratorLaws.lean / iterator-laws-r2 | 0 | 1.31 | 2572224 | 0 |
| AspisR17MaskSource/AuditCaller.lean / mask-audit-r3 | 0 | 1.11 | 2567064 | 0 |

Audit r2 added actual_map_step but failed to rewrite the projected range
dictionary; its sorryAx diagnostic was NOT accepted. R3 first normalizes the
premise to the concrete range-next declaration and succeeds, with one harmless
unused-simp-argument warning. Laws r2 removes the r1 unused simp arguments.
No unchanged failing target was rerun or given a larger memory limit.

Compiled propositions:

- `actual_closure_body`: the schematic closure body is definitionally the
  typed generated closure, with its unused Usize argument retained.
- `actual_closure_closed`: closure write-back specialization to actual
  generated QM31 multiplication, retaining failure and divergence.
- `actual_map_step`: under the EXPLICIT range-next premise, the actual closure
  emits oldPower and retains (newPower, node), including multiplication failure.
- `zipMutNext_some`: exact retained write-back for the successful pair case.
- `zipMutNext_forward`: dropping only the returned backward function from the
  observation agrees with the cached ordinary Zip::next model for all inputs,
  including failed/divergent results. This is NOT a Rust specialization theorem.

Final #print axioms for the typed closure/map lemmas, mixing_row, all four
loops and mask_weights: `[propext, Classical.choice, Quot.sound]` only.
Map-next some and zip-some use propext/Quot.sound; map-next none uses propext;
collector and zip-forward use the standard three. No sorryAx or external
iterator/security assumptions remain in these accepted targets. An axioms
audit of executable definitions does NOT prove that they refine Rust or
terminate, nor that their output satisfies the retained mask specification.

The existing generated Types and unchanged compiled dependencies were reused
after byte comparison, not replayed. Final reproducible stage is
`/home/dombarker/project-offloads/aspis-r17-mask-extract.aRLUCU/iterator-r2`;
the earlier compile workspace is iterator-r1 (first adapter compiled in
types-r1). Generator creation and --check both exit 0; final sources compare
equal to the compiled sources before copying their oleans. SHA256s:

- Funs: 056d1e552790ac0164909ea321ac6275a89f94ba98b7569d6ae74dc63e83f514;
- IteratorCompat: 71d14a05713d2a1dcc2ecf1b611b6cc20cb440f24e9c544f703b73d952fcf0cf;
- IteratorLaws: 7bce0fb0250e2b25ac297211efb83d420e73bfeb6418b8345578b5dd3b4190ca;
- AuditCaller: 5fd674453f5e4a4355f35549ba5077d80a8b2049423be1af08c6310f84179ab2.

`run_iterator.sh` pins the relevant runtime Ops/Iter/SliceIter/VecIter,
mathlib revision and closure leaf, and compiles one allowlisted target. Run
the generator's --check before invoking it; never treat unchecked staged
edits as source-locked evidence.

First remaining source proposition: justify collectState's output/state
semantics and the concrete Rust mutable zip/collection specialization, then
prove the actual caller's bounded reverse writes and accumulation refine the
retained mask model. The fresh full-runtime field namespace still needs a
proved connection to the earlier arithmetic projection; name/body similarity
alone is insufficient. Full-transcript privacy, malicious-prover soundness,
shared-oracle/seed expansion, failures/retries/publication and explicit losses
remain open. This milestone clears compilation, not those release gates.

## Actual generated types and closure write-back boundary — 2026-09-21

Base revision `b6e87f86` plus this changeset. GitHub's privacy branch was
read-only verified at that exact commit before continuing. The preceding
soundness-answer turn was informational, not repair progress.

Inspection of the pinned raw Funs reveals MORE than the two external holes:
generated FnMut.call_mut returns `value × closure × (closure → closure)`,
but cached Core/Ops.lean expects `value × closure`. Generated FnOnce.call_once
returns `value × closure`, whereas the cached trait expects just value.
The mixing_row caller destructures pairs from map and collect, but their
external-template/runtime signatures respectively return just Map and Vec.
The mutable zip loop also carries a write-back, requiring its own inspection.
Consequently, supplying two ordinary map definitions alone would not make the
actual caller type-correct or establish borrow semantics. No silent erasure
or replacement of the generated caller was performed.

New `MaskClosureWriteback.lean` checks the exact generated call_mut BODY,
abstracting only `field.QM31.mul` into a result-valued multiplication argument.
The unused Usize argument and concrete type are schematic here; this is NOT
yet a typed invocation of the generated closure. `check_closure.py` pins the
whole raw Funs file and rejects changed multiplication order or captured-node
write-back. The compiled theorem proves that applying the returned backward
function to its updated closure gives `(oldPower, (newPower, fixedNode))`,
with multiplication failure/divergence preserved. A compiled negative
regression shows an arbitrary write-back cannot simply be discarded.
This supplies the specific borrow-closing algebra needed by a future adapter,
not a generic permission to drop back functions and not a compiler theorem.

Actual generated Types.lean compiled after ONLY narrowing `import Aeneas`
to `import Aeneas.Std.Scalar.Core`; all declarations remain byte-identical.
The reproducible `check_types.sh` validates the raw pin and stages this one
mechanical import change in a fresh task directory. No template axiom was
imported. `AuditTypes.lean` reports no axioms for M31, CM31, QM31 and the
mixing-row closure type. No actual-source Funs compilation is claimed.

Cached Linux Lean 4.32.0, one job; scopes all MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64. No other task scopes were running at preflight.
Closure leaf uses -M1800; new concrete-runtime Types/audit targets use the
preselected -M3200 budget. No memory failure or raised-cap retry occurred.

| Exact target / scope suffix | Exit | Wall s | Peak RSS KiB | Swaps | Axioms |
| --- | ---: | ---: | ---: | ---: | --- |
| AspisV8R17/MaskClosureWriteback.lean / aspis-r17-closure-r1 | 1 | 0.60 | 1560828 | 0 | failed negative-test `decide`; sorryAx output NOT accepted |
| AspisV8R17/MaskClosureWriteback.lean / aspis-r17-closure-r2 | 0 | 0.61 | 1571372 | 0 | all three theorems: propext only |
| AspisR17MaskSource/Types.lean / aspis-r17-mask-types-r1 | 0 | 0.86 | 2114700 | 0 | audited next |
| AuditTypes.lean / aspis-r17-mask-types-audit-r1 | 0 | 0.80 | 2093036 | 0 | four types: none |

The failed negative-test proof lacked a Decidable instance on Result;
replacement uses structural simplification, not an added assumption.
Host artifacts remain in `aspis-r17-mask-extract.aRLUCU/closure-r1` and
`types-r1`. SHA256s:

- final MaskClosureWriteback.lean: 953ea55acef72a5f414d54f3ac23ca1f194df891fea962bbfbda3de26d40ed65;
- staged Types.lean: 2809688293649c159ae2a8e976b1c1efd61a5ec865770609e04d926bc971c548;
- cached Core/Ops.lean inspected: f5d4a2e02ad41205d05a707ef345297194928a9340bc6e8cf03c349065c855d2;
- cached Core/Iter.lean inspected: 37e6d1901461e1df84f87a753ca3452eec4885e0779a12046630f5e26ea86985;
- pinned nightly Rust iter/adapters/map.rs inspected: f1e47647ac44777030c282423e3aefb810629dfedca161cef56cff8ef74a03ad;
- pinned nightly Rust iter/traits/iterator.rs inspected: db43b7acc33fca53d85fef3ddea29ec9f8c1e768df428676fe2de160f21d5f6b.

Rust Map::new stores iterator/closure; Map::next calls next on the underlying
iterator and applies the mutable closure only to Some. This source inspection
is guidance for the external model, not proof that cached Vec collection or
specialized iterator dispatch refines all Rust execution.

First remaining proposition: instantiate a borrow-aware adapter for the
ACTUAL generated mixing_row closure (including FnOnce/map/collect shapes),
then justify the mutable zip write-back and compile the full caller without
external axioms. Bind the new field namespace to proved arithmetic, and prove
the real loop invariants afterward. Global privacy, adversarial soundness,
shared oracle, retries and publication remain open; production and all
existing negative regressions are unchanged.

## Actual R17 mask caller extracted; iterator model boundary — 2026-09-21

Base revision `b6f3b236` plus this changeset. Read-only search confirmed the
cached V7 generated namespace has no R17 mask_weights definition. The current
research module and staged v19 module match SHA256
`147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6`.
The current field source still matches the retained 5795495e... pin.

New tools/r17-mask-extraction wires those UNCHANGED files into a minimal
aspis-core library. Only module wiring is new: field is public; corelib
reexports it so the original research module imports resolve. No function
body normalization, production edit or source-pin waiver occurred. The
dependency-free crate permits focused real-source extraction, not a model
substitution. The cached Rust toolchain is nightly-2026-06-01; Charon binary
SHA256 b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c;
Aeneas binary SHA256 e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813.

Authoritative Linux artifacts are under
`/home/dombarker/project-offloads/aspis-r17-mask-extract.aRLUCU`:
`extraction-r1/source`, `extraction-r1/output/R17MaskWeights.llbc`, and
`lean-r1/AspisR17MaskSource`. Charon targeted
`crate::r17_structured_g::mask_weights`, preset aeneas, MIR built, default
sysroot, offline/locked/release/lib/no-default-features. Aeneas used sequential,
abort-on-error, Lean backend, split-files, emit-json and AspisR17MaskSource
namespace. Both ran in MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0,
TasksMax=128 scopes, with one Cargo job; time was compilation/translation,
not a dense arithmetic gate.

| Target | Scope | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| Actual mask_weights to LLBC | aspis-r17-mask-charon-r1 | 0 | 1.02 | 223072 | 0 |
| LLBC to raw Lean | aspis-r17-mask-aeneas-r1 | 0 | 1.23 | 122848 | 0 |

Artifact hashes:

- LLBC: c79b46f32bf26d893339ec9d7160098e71c266d75423c0689ae57a03ed9ace6f.
- Types.lean: 51e47fa8908d7776913478ae49e944d4de16777d9966fc33eadc50935c0e3554.
- Funs.lean: e8b29608ef90d72b4dd3d8b0697f6619fb0e4896fdb475cdd8725fff4cc80fa3.
- FunsExternal_Template.lean: 737c12e2468f69e81b535420946279ee2645d6e09503261e7b20295322539a7b.

The real mask function and four loop bodies are present in Funs.lean. The
translation warns that runtime trait metadata lacks map/zip/collect/rev
fields and emits TWO external axioms: Iterator.map.default and Map.next.
These are not accepted premises. No generated Lean target was compiled and
no #print axioms security result is claimed. The template remains archival,
not renamed into the imported FunsExternal module. Initial read-only use of
`charon --version` was rejected by its CLI; recorded binary pins, not that
command, identify the toolchain.

First remaining source obligation: supply justified map-construction and
map-next semantics compatible with the captured mixing-row closure, inspect
the warned iterator dispatches, then compile the generated types/caller and
bind this fresh field namespace to the proved arithmetic projection.
Only then prove reverse array writes and final accumulation refine the
retained mask model. Global privacy/soundness and source-tool correctness
remain separate open obligations. No axioms, production edits, deployment,
wallet operations or negative-regression removal were introduced.

## Generated zero/one and pinned half-word model — 2026-09-21

Base revision `ec9195c8` plus this changeset. GeneratedQM31Constants.lean
authenticates the complete generated QM31.ZERO/ONE declarations (including
attributes), expanding only their closed #u32 literals. It proves canonical
limbs and decoding to actual tower zero/one. A separate halfWord is an
explicit direct model of pinned Rust `M31(0x4000_0000)`, not a newly extracted
declaration. The checker pins the complete current field.rs at
`5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8`,
checks that exact constant declaration and verifies hex-to-decimal 1073741824.
It also checks the pinned unsigned literal macro and rejects a ZERO/ONE
limb mutation and a half-word mutation.

Compiled half_value/half_canonical, half_add_half (in the actual tower),
and half_scale_correct compose the existing generated scalar operation.
The arithmetic no longer requires an unexplained half-value premise when
using this word model. Relating the actual mask caller's constant argument
to the model remains part of caller refinement, not silently assumed here.

Exact target `AspisV8R17/GeneratedQM31Constants.lean`, final SHA256
`e3654995291f35e9f66d802a0be2d2d04deeb36482eb586ba5b4567261d3f1a4`.
Cached Linux Lean 4.32.0 `-j1 -M3200`, scopes aspis-r17-constants-r1/r2,
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64:

| Attempt | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| r1, missing predicate unfolding/explicit casts | 1 | 1.12 | 2577076 | 0 |
| r2, explicit canonical unfolding and tower coordinate proof | 0 | 1.12 | 2587944 | 0 |

Final #print axioms: canonical/value lemmas use `[propext]`; zero/one
decoding and half_add_half use `[propext, Quot.sound]`; half_scale_correct
uses `[propext, Classical.choice, Quot.sound]`. No sorryAx/new assumptions.
This dependent composition target uses the same preselected limit as its
runtime/tower predecessor; no memory-failed job was retried or cap raised.

First remaining source proposition: actual mask_weights point reads,
reverse-round writes and final accumulation refine the retained mutation
model using these operations/constants, with canonical inputs and all
checked failures accounted for. The broader source-extraction, privacy,
oracle/retry/publication and soundness boundaries remain unchanged and open.
Production paths and negative regressions are untouched.

## Generated QM31 execution composed with tower arithmetic — 2026-09-21

Base revision `a3ccf38c` plus this changeset. GeneratedQM31Tower.lean now
combines the authenticated current Result graphs and the concrete tower
decoder in the same compiled theorem. mul_correct, square_correct,
add_correct and sub_correct prove successful execution, canonical output,
and equality to actual tower multiplication/squaring/addition/subtraction
for canonical inputs. scalar_correct proves the corresponding scalar
embedding multiplication for every input word, using the stronger M31
product domain. There is no assumed execution-success or formula seam.

This new composition target intentionally uses `-M3200` from its first
attempt: prior focused leaves had already established their mathematical
and runtime predecessors, while this target imports their union. Inspection
showed direct theorem composition rather than generated numeric reduction.
It is NOT an unchanged failed target retried with a higher cap. Existing
targets retain `-M1800`; no prior memory-failed target was rerun. The caller
scope remains MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64.

Exact target `AspisV8R17/GeneratedQM31Tower.lean`, cached Linux Lean 4.32.0
`-j1 -M3200`; scopes `aspis-r17-generated-tower-rN`:

| Attempt | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| r1, unresolved implicit word-pair inference in subtraction | 1 | 1.15 | 2574488 | 0 |
| r2, explicit decoder arguments | 0 | 1.09 | 2583740 | 0 |
| r3, added scalar_correct | 0 | 1.34 | 2589048 | 0 |

Final #print axioms: mul/square/scalar use
`[propext, Classical.choice, Quot.sound]`; add/sub use
`[propext, Quot.sound]`. No sorryAx or new assumption. Generated declaration
authentication and existing negative mutation controls passed in each run.

First remaining source obligation: bind the actual mask caller's constants,
canonical input conditions and array/loop execution to this operation
interface and the retained MaskWeightWrites model. This is still a
source-projected arithmetic theorem, not certification of the entire
extraction pipeline. Field/nonresidue integration, source transcript
distribution, shared-oracle/retry/publication privacy and protocol-level
malicious-prover soundness remain open. Production paths and negative
regressions are unchanged.

## Concrete shared-word decoder into the actual tower — 2026-09-21

Base revision `c74f0439` plus this changeset. QM31WordTower.lean instantiates
the actual quadratic tower over ZMod P and proves decode_mul, decode_square,
decode_add and decode_sub for the SAME shared Nat word formulas used by the
generated execution theorems. Product/square/add decoding is unconditional;
subtraction retains the canonical-subtrahend premise. embed_product and
embed_square are definitional identifications of residue-coordinate formulas
with the retained tower algorithms, followed by the compiled ring identities.
No cardinality-only equivalence or hidden field assumption is substituted.

RawReducerNat, QM31WordFormulas and QM31WordResidues now use module-scoped
public interfaces, with exposed definitions and private tactic imports.
Their mathematical statements/bodies are unchanged. The initial bridge
attempt correctly rejected importing a non-module dependency; converting
this three-leaf pure dependency chain resolved it. Aeneas source projections
remain non-module and were not modified by this migration.

Cached Linux Lean 4.32.0 `-j1 -M1800`, each scope MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, TasksMax=64. Targets below are under
AspisV8R17; scope names have prefix aspis-r17-:

| Target | Scope suffix | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| QM31WordTower.lean, non-module import rejection | concrete-tower-r1 | 1 | 0.23 | 645700 | 0 |
| RawReducerNat.lean | module-RawReducerNat-r1 | 0 | 0.51 | 536580 | 0 |
| QM31WordFormulas.lean | module-QM31WordFormulas-r1 | 0 | 0.28 | 522224 | 0 |
| QM31WordResidues.lean | module-QM31WordResidues-r1 | 0 | 0.79 | 1008808 | 0 |
| QM31WordTower.lean | module-QM31WordTower-r1 | 0 | 0.79 | 1206840 | 0 |
| UnsignedReducerExecution.lean | module-consumer-UnsignedReducerExecution-r1 | 0 | 0.75 | 1629900 | 0 |
| GeneratedQM31Products.lean | module-consumer-GeneratedQM31Products-r1 | 0 | 0.71 | 1634648 | 0 |
| GeneratedQM31Linear.lean | module-consumer-GeneratedQM31Linear-r1 | 0 | 0.75 | 1627764 | 0 |

All six bridge #print axioms results are `[propext, Quot.sound]`. Rechecked
reducer and product consumers retain the standard three axioms; linear and
residue leaves use `[propext, Quot.sound]`, with mul_canonical axiom-free.
No sorryAx or cap increase. Source checks and negative mutations passed.
The consumer reruns are justified by the changed dependency interfaces,
not an unchanged full regression.

First remaining composition: put the generated Result execution and this
decoder together in the checked source-operation theorem (including scalar
multiplication/constant), then bind actual mask arrays/loops and canonical
input invariants. Field/nonresidue integration, complete extraction-pipeline
certification, full-transcript privacy and malicious-prover soundness bounds
remain separate. Production paths and negative regressions are unchanged.

## Actual quadratic-tower ring identities — 2026-09-21

Base revision `ca11059d` plus this changeset. QuadraticTowerOperations.lean
uses the actual Mathlib QuadraticAlgebra type/operations with first relation
i²=-1 and second relation u²=2+i. It replays the retained Karatsuba,
extension-constant and square proof route over an arbitrary commutative base
ring. cmul_eq/cr_eq/qmul_eq/qsquare_eq identify the explicit formulas with
the actual tower multiplication, not with componentwise pair multiplication.
This needs no nonresidue/field axiom: these are ring identities. The concrete
ZMod instantiation and composition with QM31WordResidues are still next.

Exact target `AspisV8R17/QuadraticTowerOperations.lean`, final SHA256
`48fe57215f6f386dd5101d4006f8d31969efebe5a6505eeda19c03b0589d8192`.
Cached Linux Lean 4.32.0 `-j1 -M1800`; scopes `aspis-r17-tower-ops-rN`,
all MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64:

| Attempt | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| r1, Defs plus broad Ring import, import-memory failure | 134 / signal 6 | 1.72 | 2000808 | 0 |
| r2, Ring.Basic instead, import-memory failure | 134 / signal 6 | 1.74 | 2001008 | 0 |
| r3, module/public interface with private tactic import, two reassociation goals | 1 | 1.00 | 1192476 | 0 |
| r4, solved reassociation, two tactic-style warnings | 0 | 1.05 | 1203336 | 0 |
| r5, removed unnecessary sequence-focus syntax | 0 | 1.11 | 1204484 | 0 |

The memory remedy is module-scoped imports, NOT a cap increase or unchanged
higher-cap rerun. Signal-6 time footers are not success. Failed-elaboration
sorryAx output is excluded. Final #print axioms: cmul_eq and cr_eq use
`[propext]`; qmul_eq and qsquare_eq use `[propext, Quot.sound]`; no sorryAx.

First remaining proposition: the concrete shared-word decoder into this
tower commutes with all verified source operations. Then source caller
constants, canonical input invariants, actual arrays/loops, field/nonresidue
integration, full-transcript privacy and protocol soundness remain to close.
No production path, negative regression or security assumption changed.

## Product and square residue interpretation — 2026-09-21

Base revision `a6a24282` plus this changeset. QM31WordResidues now proves
decode_mul, decode_r, decode_qm_mul and decode_qm_square for the shared
exact word formulas. CM31/QM31 products and square interpretation accept
arbitrary Nat input coordinates; all modular subtrahends are canonical by
construction. The extension-constant decode_r theorem explicitly requires
canonical input, and its uses discharge that premise via mul_canonical.
No field law or probability/hiding premise was added.

The outputs are equal to explicitly defined modular coordinate operations
cMul/cR/qMul/qSquare. This connects word reduction to the retained
Karatsuba shape, NOT yet to a QuadraticAlgebra field instance. It does not
turn the pair type's ordinary componentwise multiplication into tower
multiplication. The subsequent tower identification remains mandatory.

Exact target `AspisV8R17/QM31WordResidues.lean`, SHA256
`5a302d607e8f72137002646d67cb5872f63ae16fb2fa2681f377bd0d8fd037c9`.
Cached Linux Lean 4.32.0 `-j1 -M1800`, scope
`aspis-r17-product-residues-r1`, MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64: exit 0, wall 0.96 s,
peak RSS 1840620 KiB, swaps 0. mul_canonical has no axioms; all nine
interpretation/cast #print axioms results use `[propext, Quot.sound]`.
No sorryAx, failed attempts or cap increase. Unchanged generated consumers
were not replayed because their imported formulas did not change.

Next: identify these coordinate operations with the explicit retained
quadratic tower. Import inspection shows QuadraticAlgebra.Basic also pulls
in involution/norm and FieldSimp; QuadraticAlgebra.Defs is the relevant
smaller ring-operation interface to inspect before another focused attempt.
Source caller arrays/loops, field/nonresidue certification integration,
full transcript privacy and malicious-prover soundness remain separate open
obligations. Production paths and negative regressions remain unchanged.

## Shared pure word interface and linear residue interpretation — 2026-09-21

Base revision `e0989f78` plus this changeset. QM31WordFormulas.lean separates
the existing modular Nat pair formulas from generated-runtime imports.
The CM31 product helpers are expanded definitionally; generated declarations
and theorem statements are unchanged. GeneratedQM31Products and
GeneratedQM31Linear were recompiled successfully against this shared interface.
This split lets mathematical interpretation consume exactly the same formulas
without loading Aeneas. Source authentication and negative mutations still pass.

QM31WordResidues.lean proves two- and four-coordinate addition/subtraction
interpretation in ZMod P. Addition is unconditional; subtraction requires
canonical subtrahend limbs so Nat subtraction does not silently truncate.
These are coordinatewise residue equalities, not a new tower/field instance
or an end-to-end source caller theorem.

All targets used cached Linux Lean 4.32.0 `-j1 -M1800`, systemd scopes with
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64. Scope names below
have prefix `aspis-r17-`; target paths have prefix `AspisV8R17/`.

| Target / attempt | Scope suffix | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| QM31WordFormulas.lean | word-formulas-r1 | 0 | 0.36 | 929416 | 0 |
| QM31WordTower.lean, quadratic-algebra import memory exception | word-tower-r1 | 134 / signal 6 | 1.80 | 1845456 | 0 |
| GeneratedQM31Products.lean, changed formula import | products-split-r1 | 0 | 0.72 | 1634340 | 0 |
| QM31WordResidues.lean, cast-self simplification gap | word-residues-r1 | 1 | 0.97 | 1827028 | 0 |
| GeneratedQM31Linear.lean, changed formula import | linear-split-r1 | 0 | 0.65 | 1627800 | 0 |
| QM31WordResidues.lean, wrong lemma namespace | word-residues-r2 | 1 | 0.81 | 1827140 | 0 |
| QM31WordResidues.lean, explicit ZMod.natCast_mod rewrite | word-residues-r3 | 0 | 0.84 | 1837836 | 0 |

The failed tower draft was replaced by the smaller coordinate interface,
not rerun at a higher cap or accepted as compiled. Its time footer zero is
not success; controlling exit was 134. Failed elaborations' sorryAx output
is excluded. Final five residue #print axioms results are
`[propext, Quot.sound]`; products retain the standard three axioms and
linear wrappers retain `[propext, Quot.sound]`. The formulas-only leaf
introduces definitions, no axioms/theorems. No new security assumption.

First remaining interpretation proposition: multiplication, squaring and
extension-constant/scalar formulas must map to the explicit retained tower,
using a resource-bounded algebra interface. The tower import failure does
not justify replacing its arithmetic with a cardinality-only equivalence.
Actual source mask arrays/loops and global privacy/soundness stay open.
Production paths and negative regressions are unchanged.

## Current QM31 linear wrappers — 2026-09-21

Base revision `27f24bce` plus this changeset. GeneratedQM31Linear.lean
retains the complete QM31.add and QM31.sub declarations from pinned
FunsChunk04. Composing the current CM31 results proves success, canonicality
and exact four-word modular addition/subtraction for every canonical pair
of inputs. Source authentication rejects two wrong-component mutations.

Exact target `AspisV8R17/GeneratedQM31Linear.lean`, SHA256
`b9185d993738888baf0822e20e5fdd064334554cb3d412fe5121ff872fb0f73d`.
Cached Linux Lean 4.32.0 `-j1 -M1800`, scope `aspis-r17-qm31-linear-r1`,
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64:
exit 0, wall 0.76 s, peak RSS 1631908 KiB, swaps 0. Both #print axioms
results are `[propext, Quot.sound]`; no sorryAx, failed attempts or new
assumptions. Existing product/scalar/mul_by_r authentication also passed;
unchanged Lean targets were not recompiled.

The precise next arithmetic interpretation is the retained
`AspisFormal/V5ComponentCQM31TowerExact.lean` explicit tower
`CM31 = ZMod P[i]/(i²+1)`, `QM31 = CM31[u]/(u²-(2+i))`, whose coordinates
are the four source limbs. The older cardinality-only Galois-field
representation is NOT an arithmetic correspondence. This turn inspected
the retained tower, not recompiled or source-instantiated it. Its large
representation/sampler import closure should not be pulled into the focused
runtime leaf; use a small justified arithmetic interface or split first.

Next proposition: interpreting the current exact modular-word operation
formulas in that explicit tower commutes with add/sub/mul/square/scalar
multiplication. Actual source mask-loop/array refinement and all global
privacy/soundness obligations remain open. No production code or negative
regression changed.

## Complete current QM31 product graphs — 2026-09-21

Base revision `134d3e7b` plus this changeset. GeneratedQM31Products.lean
retains the complete generated QM31.mul and QM31.square declarations from
pinned FunsChunk04. It composes every checked CM31 operation, discharging
all intermediate success/canonicality conditions. For all canonical inputs
the complete Result is successful, the four output limbs are canonical,
and their values equal explicit pure Nat modular-word formulas qmMulWords
and qmSquareWords. The square proof uses the already compiled current
CM31.square = CM31.mul-self theorem, not an assumed equality.

The word formulas deliberately retain the source's Karatsuba/subtraction
and extension-constant structure. They are NOT yet an equality to the
abstract extension-field multiplication used by MaskWeightWrites. Their
interpretation and the source-to-model caller bridge remain distinct tasks.

Exact target `AspisV8R17/GeneratedQM31Products.lean`, SHA256
`674aa22af8274146e6d37b2807236fad286bc956b471ee7fc2e06c18e5658b3f`.
Source authentication passed for both complete declarations; swapped-square
component and wrong-final-subtrahend mutations were rejected, alongside
the existing type/scalar/mul_by_r checks. Cached Linux Lean 4.32.0,
`-j1 -M1800`, scope `aspis-r17-qm31-products-r1`, MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, TasksMax=64: exit 0, wall 0.74 s,
peak RSS 1636896 KiB, swaps 0. Both #print axioms results are
`[propext, Classical.choice, Quot.sound]`, with no sorryAx/new assumptions.
No failed attempts or resource-cap increases.

Next: bind the remaining QM31 linear wrappers and interpret the exact
four-word products in the retained extension-field model. Then connect
the source constant, actual mask arrays/loops and opening callers. Full
extraction-pipeline certification, joint-view privacy, shared-oracle and
retry/publication arguments, and protocol soundness losses remain open.
Production protocol paths and negative regressions are unchanged.

## Current extension-constant multiplication — 2026-09-21

Base revision `58e9836c` plus this changeset. GeneratedMulByR.lean retains
the complete pinned FunsChunk04 mul_by_r declaration and composes the checked
M31 double/sub/add theorems. For every canonical CM31 input it proves
successful Result execution, canonical outputs and the exact intermediate
word formulas, then normalizes them to signed real residue `2a-b` and
imaginary residue `a+2b`. Intermediate canonicality is discharged explicitly;
no success or arithmetic-operation premise is assumed.

The checker authenticates the declaration and rejects sign and component
mutations. Target `AspisV8R17/GeneratedMulByR.lean`, SHA256
`a4ade35114e2f7af067842d6c02134c1b04c71535df152d85d3cbbe5c6b1f26c`.
Cached Linux Lean 4.32.0 `-j1 -M1800`, scope `aspis-r17-mul-by-r-r1`,
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64:
exit 0, wall 0.74 s, peak RSS 1636008 KiB, swaps 0.
All four #print axioms results are `[propext, Quot.sound]`. No sorryAx,
new assumption, failed compilation or higher-cap retry.

The next arithmetic theorem must compose the complete QM31 multiplication
and square graphs from these CM31 dependencies, not merely infer correctness
from their names. Mapping the resulting word formulas into the retained
extension-field model, the mask caller's arrays/constant, source extraction
pipeline and all global privacy/soundness obligations remain separate.
No production path or negative regression changed.

## Current QM31 scalar multiplication — 2026-09-21

Base revision `14c11623` plus this changeset. GeneratedQM31Scalar.lean
retains the current QM31 type and complete CM31.mul_m31/QM31.mul_m31
declarations. The new checker authenticates these against pinned Types.lean
and FunsChunk06.lean and rejects type/component mutations (three controls).
The composed theorem proves successful checked execution, canonical output
and exact four-coordinate modular products for ALL input words, without
assuming canonical inputs; this stronger domain follows from the retained
all-U32 M31 multiplication theorem.

The separate qm31_half_scalar theorem requires canonical x and explicitly
`s.val = 1073741824`. It proves that doubling each resulting coordinate
recovers the input coordinate modulo P. Its generic modular arithmetic
lemma is compiled, not assumed. The Rust source declares
`pub const M31_HALF: M31 = M31(0x4000_0000);`; the actual caller's constant
construction is not yet a compiled source binding, so the value premise
is not silently discharged here.

Exact target `AspisV8R17/GeneratedQM31Scalar.lean`, SHA256
`e650b5f4c41c81c409a03c5a8afa3d5990024b3e1440980dd5c3eacafee722e8`.
Cached Linux Lean 4.32.0 `-j1 -M1800`, systemd scope
`aspis-r17-qm31-scalar-r1`, MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0,
TasksMax=64: exit 0, wall 0.72 s, peak RSS 1634472 KiB, swaps 0.
#print axioms: half_scalar_double uses `[propext]`; cm31_scalar_words,
qm31_scalar_words and qm31_half_scalar use
`[propext, Classical.choice, Quot.sound]`. No sorryAx, new assumption,
failed compilation or cap increase.

First remaining arithmetic composition: authenticate/compose QM31
add/sub/mul/square and mul_by_r into the retained extension-field formulas,
then bind the source constant and actual mask_weights arrays/loops. The
current result is a source-projected scalar theorem, not a proof of the
whole mask caller, the extraction pipeline, privacy or protocol soundness.
Production code and negative regressions remain unchanged.

## Current CM31 linear operations and caller dependency check — 2026-09-21

Base revision `47bfb1de` plus this changeset. Inspection of the actual
`r17_structured_g.rs:69` mask_weights body confirms that its K type is QM31:
the round block uses add/sub/mul/square and the reverse scale uses
`mul_m31(M31_HALF)`, NOT a call to half. Consequently, the completed M31/CM31
half proof alone cannot close this caller. QM31 operation correspondence,
the scalar half constant, and checked array/loop semantics remain required.

`AspisV8R17/GeneratedCM31Linear.lean` now retains the complete generated
CM31.add, CM31.sub and CM31.double declarations from pinned FunsChunk04.
It composes the current M31 proofs to establish successful execution,
canonical output coordinates and exact modular word formulas for every pair
of canonical CM31 inputs. The subtraction result is additionally normalized
to signed integer remainders, avoiding an invalid truncated-Nat interpretation.
The canonicality predicate is explicit and is not asserted for arbitrary
unvalidated input words.

The extended source checker authenticated all three declarations and rejected
three component/operation mutations, as well as checking the existing
M31 add/sub and reducer dependencies. Leaf SHA256:
`f514a4cbda54569c9c154c0bf4810285ef64989e9edae432774205548d2440a8`.

Exact focused target `AspisV8R17/GeneratedCM31Linear.lean`, cached Linux
Lean 4.32.0 `-j1 -M1800`, scope `aspis-r17-cm31-linear-r1`, MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, TasksMax=64: exit 0, wall 0.73 s,
peak RSS 1637180 KiB, swaps 0. All five #print axioms results are
`[propext, Quot.sound]`; no sorryAx, new assumptions or failed attempts.

First remaining arithmetic composition: the current QM31 operations used
by mask_weights, including mul_by_r and mul_m31, must refine the retained
extension-field formulas while preserving canonicality. Then the actual
271-entry writes, point reads and 1024-entry accumulation must be connected
to MaskWeightWrites/SourceMixingWeights. Source-projection authentication
does not certify the full extraction pipeline or any full privacy/soundness
claim. Production paths and negative regressions remain unchanged.

## Current generated halving execution — 2026-09-21

Base revision `a4bdbc72` plus this changeset. GeneratedM31Half.lean retains
the generated FunsChunk06 M31.half and CM31.half declarations, with only the
closed #i32/#u32 literals expanded to their authenticated constructors. It
proves successful Result execution, canonical outputs and the inverse-of-two
property on every canonical input (both components for CM31), composing the
signed runtime shifts with the retained HalfRotateNat theorem. In particular,
signed counts are not silently replaced with unsigned counts.

`check_r17_half.py` pins FunsChunk06 at
`f57cf84b503d6c0f03199a951872f3676bd7c9dcc644416372ab8289e6b52b9e`,
the existing runtime files and Notations.lean. Seven signed literal blocks and
three operator instances are byte-authenticated. One ofIntCore bounds proof
is explicitly adapted: its executable modulo/toNat/BitVec construction and
type are unchanged; the checker permits only the specified proof replacement.
The bound_suffices helper retains the runtime statement with a direct proof.
The exact #i32 and #u32 macros are checked; their closed bounds are decidable
without the scalar_tac fallback. Literal proof irrelevance is compiled.
The checker rejects two literal mutations and two generated-half mutations.
It remains a source projection, not a full extraction-pipeline certificate.

Focused cached Linux, Lean 4.32.0 `-j1 -M1800`; each systemd scope has
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64:

| Exact target | Scope suffix (prefix aspis-r17-) | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| AspisV8R17/SignedLiteralSupport.lean, original proof missing imports | signed-literal-r1 | 1 | 0.99 | 1792416 | 0 |
| Same target, expanded import set, memory exception before proof checking | signed-literal-r2 | 134 / signal 6 | 1.79 | 1941004 | 0 |
| Same target, core bounds-proof replacement | signed-literal-r3 | 0 | 0.84 | 1633752 | 0 |
| AspisV8R17/GeneratedM31Half.lean | generated-half-r1 | 0 | 0.70 | 1633864 | 0 |

The memory-failed attempt was not rerun at a higher cap. Its time footer's
zero is not success: the controlling process returned 134 and reported signal
6. Failed-attempt error-generated sorryAx is excluded. All final literal and
generated-half #print axioms results are `[propext, Classical.choice, Quot.sound]`,
with no sorryAx or new assumptions. A subsequent source comment clarification
does not change any declaration. Generated leaf SHA256:
`e9961f4cee08a1e3a7e3cfabe5dbc3bc4e075b392e28c6546d52891e139cba8b`.

This closes the changed halving primitive's projected execution obligation,
alongside the existing current mul/square results. First remaining source
composition obligation: the actual R17 mask/opening field and array callers
must refine the retained algebraic identities on all reachable canonical
states, including checked index/length/failure behavior. This does not close
joint transcript privacy, commitment extraction, shared-oracle chronology,
retry/publication or the end-to-end malicious-prover soundness bound. No
production protocol paths or negative regressions changed.

## Signed shift runtime projection — 2026-09-21

Base revision `b3bb9a6c` plus this changeset. SignedShiftSlice.lean authenticates
nine declaration bodies against the pinned Core.lean and Bitwise.lean runtime:
signed scalar type/width/representation/value/toNat, left shift, both unsigned
word shifts with signed counts, and OR. The toNat automation attributes are
intentionally omitted; its body is identical. This remains a source projection,
not a full-runtime elaboration/caller refinement theorem.

The focused proofs establish exact right-shift values, left-shift values modulo
word width for nonnegative in-range counts, failure for negative counts, and
the OR value identity. The checker rejects three mutations (sign guard, width
guard, OR changed to AND) and preserves the existing source pins.

Exact target `AspisV8R17/SignedShiftSlice.lean`, cached Linux Lean 4.32.0,
`-j1 -M1800`; systemd scopes `aspis-r17-signed-shift-r1/r2`, each
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64:

| Attempt | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial missing Int notation import and implicit-argument misuse | 1 | 0.77 | 1624460 | 0 |
| Added Int notation import; corrected toNat_shiftLeft application | 0 | 0.71 | 1633692 | 0 |

Final SHA256 `39d1d64c4fcadb6fa2a7b76ea6a7f244fe3196786711f9a7800d6943d3135a93`.
Final #print axioms: right_success and or_value use `[propext, Quot.sound]`;
left_success and negative_counts_fail use `[propext]`. The failed attempt's
error-generated sorryAx is not release evidence; final compilation has none.

First remaining primitive proposition: authenticate the signed literal
constructors for 1#i32 and 30#i32 and the generated FunsChunk06 M31.half body,
then compose its actual Result graph with HalfRotateNat. No generated caller
equality, production change, global privacy or soundness claim is made here.

## Focused retained halving mathematics — 2026-09-21

Base revision `52742af4ca4b5d3da3aa798ead8043b20471681f` plus this changeset.
`AspisV8R17/HalfRotateNat.lean` replays the retained LineNorm low-31 rotate
argument with core imports instead of Mathlib.Tactic. It proves the arithmetic
formula, canonical range, intermediate word ranges, and the added consequence
`(2 * halfWord x) % p = x` for every `x < p`. This is a Nat theorem, not yet
a theorem about successful execution of generated M31.half.

Focused cached Linux host, Lean 4.32.0, `-j1 -M1800`, systemd scopes
`aspis-r17-half-nat-r1` and `aspis-r17-half-nat-r2`, each MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, TasksMax=64:

| Exact target | Change | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| AspisV8R17/HalfRotateNat.lean | Retained three lemmas | 0 | 0.40 | 808584 | 0 |
| AspisV8R17/HalfRotateNat.lean | Added half_double_mod | 0 | 0.37 | 810792 | 0 |

`#print axioms`: half_arithmetic uses `[propext, Quot.sound]`; the range,
word-range and modular-double theorems use
`[propext, Classical.choice, Quot.sound]`. No sorryAx or new assumption.
The runner's existing FunsChunk04 authentication still passes, but does NOT
authenticate half: that declaration is in FunsChunk06 and uses signed i32
shift counts. The first remaining primitive obligation is to authenticate
that declaration and its literal/shift semantics, then prove its successful
word execution equals halfWord. Full field/array caller composition,
commitment extraction, shared-oracle chronology, retries/publication and
end-to-end privacy/soundness remain open. No production paths changed.

## Current CM31 square and equality to self multiplication — 2026-09-21

Base `b1a67fdd5385b51b5899422dbf00542248b314aa` plus this changeset.
GeneratedCM31Square.lean retains the full current generated square declaration,
including attributes, byte-for-byte. The checked U64 operand proof covers both
additions, subtraction without underflow, and multiplication without overflow
for canonical a,b. It then composes the reducer, base multiplication and doubling
to prove successful canonical output. Its exact words are
`((a+b)*(a+P-b))%P` and `((a*b)%P+(a*b)%P)%P`.

GeneratedCM31SquareNormalized.lean proves these are `(a*a-b*b) mod P` using
SIGNED Int subtraction and `(a*b+a*b) mod P`. It also proves the full Result
identity `CM31.square x = CM31.mul x x` on canonical limbs, by equality of the
canonical output words, not merely by comparing a fixture. All intermediate
success premises are discharged. The square is not inferred from multiplication;
its distinct generated execution graph is proved first.

Source hashes:

- GeneratedCM31Square: `6e783cb37c8a88fa774ac8415b4b73a654ef739d8d07d6af23a5fb6b9f96065d`.
- GeneratedCM31SquareNormalized: `d100cd8da24014e36b23d188cfb9c0958480b1ec882244ba2805275d6a9e2d5a`.

The checker matched the square declaration against pinned FunsChunk04.lean,
rejected subtraction-sign and doubling-input mutations, and passed the existing
literal/reducer authentication, exit 0. Imported literals retain the earlier
explicit macro-expansion boundary. No whole-caller extraction replay is claimed.

Focused host evidence, Lean 4.32.0 `-j1 -M1800`, MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64, no warnings or failed attempts:

| Exact target | Scope suffix (prefix aspis-r17-) | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| AspisV8R17/GeneratedCM31Square.lean | generated-square-r1 | 0 | 0.82 | 1637864 | 0 |
| AspisV8R17/GeneratedCM31SquareNormalized.lean, residue result | square-normalized-r1 | 0 | 0.78 | 1637084 | 0 |
| Same target, new equality-to-self-multiplication theorem | square-normalized-r2 | 0 | 0.77 | 1639556 | 0 |

Audits: squareOperand_success, generated_square_graph, square_real_int and
square_imag_mod use `[propext, Quot.sound]`; generated_square_words,
generated_square_complex_residues and generated_square_eq_mul_self use
`[propext, Classical.choice, Quot.sound]`. No sorryAx, new assumption or cap increase.

The changed CM31 mul/square arithmetic now has current-source projected execution
and standard modular-coordinate proofs. This is NOT a protocol soundness or
privacy release gate. The earlier arithmetic-reuse audit also identified a
changed M31.half body: current field.rs uses the low-31 rotate. First remaining
primitive-source proposition is to bind that checked generated body to the
retained LineNorm.halfWord result and prove canonicality and doubling residue.
LineNorm already contains the mathematical range/double/cast lemmas; they were
located, not re-proved or recompiled here. Then the field/array adapters and
actual R17 mask/opening callers still need source composition. All joint-view,
oracle/seed, retry/publication and full-transcript obligations remain separate.
No production protocol path or negative regression changed.

## Standard complex residues and checked addition — 2026-09-21

Base `65269efce1dc42d7982c36d1070b3692db43a2d7` plus this changeset.
GeneratedCM31Normalized.lean proves that the complete generated multiplication
returns the standard complex-product residues: real `(a*c-b*d) mod P` using
SIGNED Int subtraction, imaginary `(a*d+b*c) mod P`, both canonical. It consumes
generated_mul_words directly, so successful source execution is part of the
conclusion, not an extra hypothesis. The two word-formula normalization lemmas
hold for all Nat inputs. Their audits use `[propext, Quot.sound]`; the composed
generated_mul_complex_residues audit uses `[propext, Classical.choice, Quot.sound]`.
This establishes the explicit modular coordinate specification; a named adapter
to any larger retained field/array datatype is not silently assumed.
Source hash: `6fd573cd30e5a302964186679742565c3101945be7034a26886e63ce9c8810df`.

GeneratedM31Add.lean copies current M31.add and M31.double, attributes included,
and proves exact canonical sum/double remainders on canonical inputs. Both
audits use `[propext, Quot.sound]`. The checker matched the two declarations
against pinned FunsChunk04.lean, rejected sign/double-argument mutations, and
passed the existing literal/reducer text checks, exit 0. Source hash:
`c509d0c36918dd113a49320004b1959b1e79feaf332ff1151561b04bbdee1cba`.

Both focused targets compiled on first attempts with no warnings or sorryAx.
Retained host/cache, Lean 4.32.0 `-j1 -M1800`, MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64; no cap change or full replay:

| Exact target | Scope | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| AspisV8R17/GeneratedCM31Normalized.lean | aspis-r17-cm31-normalized-r1 | 0 | 0.85 | 1644512 | 0 |
| AspisV8R17/GeneratedM31Add.lean | aspis-r17-generated-m31add-r1 | 0 | 0.69 | 1634512 | 0 |

First remaining source-specific arithmetic proposition: the SEPARATE current
CM31.square implementation must execute successfully on canonical inputs,
including the unreduced `(a+b)*(a+P-b)` real operand, and return canonical
`(a*a-b*b, 2*a*b)` residues. Multiplication correctness alone does not prove
that different source body. Its multiplication, subtraction, reducer and
doubling dependencies are now available. R17 caller integration, field/array
adapters, and full privacy/soundness obligations remain open. No production
protocol path, source pin or negative regression was changed.

## Current subtraction and complete CM31 word execution — 2026-09-21

Base `c7c9e3c710cb53786142bbbb116aa409766754fd` plus this changeset.
Both new focused targets compiled on their first attempts. M31.sub and
CM31.mul are copied byte-for-byte, attributes included, from the pinned
FunsChunk04.lean. Imported reducer literals retain the explicit expansion
and constructor-proof justification documented below.

GeneratedM31Sub proves successful subtraction on canonical inputs, with
canonical output `(x.val + P - y.val) % P`. It proves both conditional branches,
the initial checked U32 addition, and both possible checked subtractions.
source_P_value uses `[propext]`; finishSub_mod and generated_sub_mod use
`[propext, Quot.sound]`. Final source hash:
`eb919af92c9138ef8834881d3d3c1f9057ff679f6fa354eed617f35e2b2318cd`.

GeneratedCM31Mul proves an unconditional Result computation-graph identity,
then successful complete execution for canonical a,b,c,d with canonical output
words. Writing A=(a*c)%P, B=(b*d)%P, C=((a+b)*(c+d))%P, those words are exactly
`(A+P-B)%P` and `((C+P-A)%P+P-B)%P`. This includes m0/m1, the actual lazy cross
fragment, its reducer, and all three coordinate subtractions; no successful
intermediate execution is left as an external premise. generated_mul_graph
uses `[propext, Quot.sound]`; generated_mul_words uses
`[propext, Classical.choice, Quot.sound]`. Final source hash:
`be1b8b1b9348552464d00a773be37c879e6ec08b5af324e89ebc749f6952523e`.

Host evidence, Lean 4.32.0 `-j1 -M1800`, MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64, no warnings or sorryAx:

| Exact target | Scope | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| AspisV8R17/GeneratedM31Sub.lean | aspis-r17-generated-m31sub-r1 | 0 | 0.74 | 1636840 | 0 |
| AspisV8R17/GeneratedCM31Mul.lean | aspis-r17-generated-cm31mul-r1 | 0 | 0.69 | 1633648 | 0 |

Source authentication matched both new complete declarations and rejected two
mutations each (subtraction sign/branch and CM31 operand/output routing), exit 0.
The existing reducer/literal/M31 multiplication text checks also passed in that
invocation. No unchanged Lean replay, memory-cap increase, production edit or
negative-regression removal occurred.

First remaining arithmetic proposition: map the two exact word formulas into
the retained field model and prove equality to `(a*c-b*d, a*d+b*c)`, connecting
the current execution theorem to the field-level CM31 specification. The current
CM31 square still needs its separate source execution theorem. These arithmetic
results do not close the R17 protocol caller or any full-transcript privacy or
soundness release gate; joint observations, oracle/retry/publication premises
remain separate and open.

## Current generated M31 multiplication — 2026-09-21

Base `90a1f61af577e0bb4e7cc38b4929192be725b9ea` plus this changeset.
Exact target `AspisV8R17/GeneratedM31Mul.lean` compiled on the first attempt.
Its source SHA-256 is
`b2c5f2991dff2d77f8f0051fbbff72140abb3e3bb87c2e321d827e283c6da24f`.
The two generated declarations (M31.mul and M31.reduce_u64) are copied
byte-for-byte, including attributes, from pinned FunsChunk04.lean. No literal
macro rewrite is needed for these declarations; their imported reducer retains
the previously documented explicit literal expansion.

Three audited results:

- cast_widen_value: current U32-to-U64 cast preserves the exact Nat value.
- generated_mul_mod: for ANY two stored U32 words, the current generated M31
  multiplication succeeds, returns `(x.val*y.val) % P`, and is canonical.
  No canonical-input assumption is needed: both U32 operands are below 2^32,
  hence their product fits U64. This uses symbolic multiplication monotonicity.
- generated_wrapper_mod: the M31 reducer wrapper succeeds for every U64 input,
  with the exact canonical remainder.

The cast audit is `[propext, Quot.sound]`; both execution audits are
`[propext, Classical.choice, Quot.sound]`. No warnings or sorryAx. Host scope
`aspis-r17-generated-m31mul-r1`, Lean 4.32.0 `-j1 -M1800`, MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0, TasksMax=64: exit 0, wall 0.65 s, peak RSS
1629996 KiB, swaps 0. No cap change or unchanged build replay occurred.

The extended source checker matched both generated declarations against the
full pinned source, rejected two multiplication/wrapper mutations, and repeated
the existing literal/reducer text checks (three negative mutations), exit 0.
This authenticates the focused source projection, not the entire extraction
pipeline or R17 caller. No production paths or negative regressions changed.

First remaining arithmetic proposition: current M31.sub must succeed on
canonical inputs and return their difference modulo P; then compose the two
base multiplications, cross-term reducer and three subtractions into the full
CM31 multiplication theorem. The square delta and end-to-end privacy/soundness
obligations remain open.

## Macro-expanded generated reducer binding — 2026-09-21

Base commit `ea475f87` plus this changeset. UnsignedLiteralSupport.lean and
GeneratedReducerExpanded.lean compiled in the retained pinned workspace.
The latter contains the original generated P constant and reduce_u64 body,
with ONLY the closed literals `2147483647#u32` and `31#u32` expanded to
`(U32.ofNat 2147483647)` and `(U32.ofNat 31)`. It retains the original
attributes, lifts, casts, checked shifts/additions, comparison and subtraction.

The constructor definitions and comparison proposition are source-authenticated.
The bound_suffices helper retains its original statement with a direct small
proof; the DecidableRel instance retains its original statement with explicit
Nat.decLe construction. These two proof implementations are NOT claimed to be
byte-identical runtime copies. No premise or scalar definition was weakened.
LiteralSupport proves constructor value, proof irrelevance, P=mask32, shift=31,
word comparison equivalence and equality of the conditional branches. Five
audits report `[propext]`; comparison_value has no axioms.

The original notation source is pinned at SHA-256
`45c40bf90ae960c24e2a82200393ceb184046be22582b428d5026d7d9577b133`.
Its #u32 macro expands to U32.ofNat with `first | decide | scalar_tac` for the
bound proof. Both closed literal bounds here succeed with decide. The literal
proof-irrelevance theorem covers any successful proof term from that macro;
the heavy scalar_tac fallback was not imported, executed or replaced by an axiom.
This is explicit macro expansion, not a claim that the original macro was replayed.

`generated_reducer_eq` proves equality to the checked reduceExecution graph for
ALL U64 inputs, including the pure-AND/lift ordering and Result bind association.
Its audit is `[propext, Quot.sound]`. `generated_reducer_mod` proves successful
execution with output exactly x modulo P and below P; its audit is
`[propext, Classical.choice, Quot.sound]`. No sorryAx appears in final targets.

The new read-only checker authenticates all pinned runtime/generated input files,
six literal-support source blocks, three operator instance blocks and two
macro-expanded generated blocks. It accepts no other generated text rewrite.
It rejected three in-memory changes (comparison orientation, shift literal,
branch condition), exit 0. Final compiled/authenticated source hashes:

- UnsignedLiteralSupport: `65f11d191b66b75ccc08c75b95f1b9fc6614d168a2abbcf1bbe2e4c128f9bf35`.
- GeneratedReducerExpanded: `8dbcaa54ce0455c1d7b8da69872d5b5a28653bf01a4451a62178a1e28de13d5b`.

All jobs used Lean 4.32.0 `-j1 -M1800`, MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0 and TasksMax=64 on nuc.local. No cap increase or whole replay.

| Target / scope suffix (prefix aspis-r17-) | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| UnsignedLiteralSupport / literal-support-r1: instance-search failure | 1 | 0.72 | 1618508 | 0 |
| UnsignedLiteralSupport / literal-support-r2: direct instance proof | 0 | 0.70 | 1627016 | 0 |
| GeneratedReducerExpanded / generated-reducer-r1 | 0 | 0.72 | 1627032 | 0 |

The first failed draft's sorryAx branch audit was rejected. Final targets had
no warnings. These results close the reducer's literal/comparison/control-flow
binding in this authenticated, macro-expanded source projection. They do NOT
authenticate the entire extraction pipeline or replay the complete current
caller. First remaining arithmetic proposition: successful current M31 mul/sub
execution and the complete CM31 coordinate reconstruction using this reducer.
The CM31 square delta and R17 caller still need composition. Full transcript
privacy and soundness remain open, with no production or negative-test changes.

## Composed checked reducer and retained-bounds split — 2026-09-21

Base `4bee9ede686290c30d147720ae8cbaf5a00aef20` plus this changeset.
`UnsignedReducerExecution.lean` now proves, for EVERY U64 input, successful
composition of two checked folds, exact U32 narrowing and the final conditional
subtraction. Output equals RawReducer.rawReduceU64, is below P, and is exactly
the input's remainder modulo P. The four audited statements are
foldExecution_success, reduceExecution_success, reduceExecution_canonical and
reduceExecution_mod. Each uses only `[propext, Classical.choice, Quot.sound]`.
Final source SHA-256:
`769cdd0b3ceab0182859cb80afd899332ff3b1972ed64b9a1cafe4e8bccfde6a`.

To avoid importing field-algebra tactics into the operational proof, the
retained Nat definitions/bounds were moved into RawReducerNat.lean. Their names,
statements and reducer definitions are unchanged; closed numeric proofs use
decide rather than norm_num. Importing core Nat bitwise lemmas instead of the
Mathlib bitwise aggregate was necessary to fit the unchanged memory cap.
RawReducer.lean imports this leaf and retains the ZMod and multiplication proofs.
No prior theorem was removed. RawReducerNat adds fold31_mod and
rawReduceU64_eq_mod_nat: the same residue argument expressed with Nat quotient
identities and linear arithmetic, without importing ZMod. Final source hash:
`d8ecc45a1dd3513557e68956d9b4b094cb0359f80c22ae9d7cae19abb9186605`.
Its four printed audits (first-fold bound, exact narrowing, canonicality,
Nat remainder) all report `[propext, Classical.choice, Quot.sound]`.

Host jobs used the retained cached workspace, Lean 4.32.0 `-j1 -M1800`,
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64. No cap increase.

| Target / scope suffix (prefix aspis-r17-) | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| UnsignedReducerExecution / reducer-execution-r1: combined algebra import OOM | 134 | 1.75 | 1990700 | 0 |
| RawReducerNat / raw-nat-r1: initial split compiled | 0 | 0.82 | 1513600 | 0 |
| UnsignedReducerExecution / reducer-execution-r2: Mathlib bitwise import OOM | 134 | 1.72 | 1890876 | 0 |
| RawReducerNat / raw-nat-r2: core bitwise imports compiled | 0 | 0.52 | 942524 | 0 |
| UnsignedReducerExecution / reducer-execution-r3: composition compiled | 0 | 0.69 | 1629852 | 0 |
| RawReducerNat / raw-nat-r3: Nat modulo proof needed explicit P unfolding | 1 | 0.51 | 934284 | 0 |
| RawReducerNat / raw-nat-r4: final Nat residue proof compiled | 0 | 0.56 | 942548 | 0 |
| UnsignedReducerExecution / reducer-execution-r4: final remainder corollary | 0 | 0.72 | 1626700 | 0 |

Memory failures were Lean interpreter exceptions, not successful compiles.
The failed Nat modulo draft's sorryAx audit was rejected. All final targets
above compiled without warnings. Existing RawReducer.lean was also checked in
the local pinned Lean workspace after each dependency revision: exit 0, 10.25 s,
1619017728 bytes RSS, zero swaps initially; final exit 0, 9.90 s,
1624408064 bytes RSS, zero swaps. Its canonicality/residue/multiplication audits
use the standard three axioms, and residue_rawM31Add uses propext/Quot.sound.
These were focused changed-dependency checks, not full manifest replays.
The dependent SourceLazyCM31.lean then compiled locally: exit 0, 5.06 s,
1629929472 bytes RSS, zero swaps, no warnings; all five printed audits contain
only `[propext, Classical.choice, Quot.sound]`.

Boundary: reduceExecution composes authenticated runtime operations but uses
explicit ofNatCore constants and a Nat-value comparison. It does NOT yet prove
equality to the complete generated reduce_u64 declaration. The first remaining
source-specific obligation is binding the generated #u32 literals, constant P,
word comparison, lifts and operation order to this composition. In particular,
foldExecution evaluates the pure AND at the addition rather than before the
checked shift; the equality must justify that reordering. Only then may this
result be used as a full extracted reducer theorem. CM31 reconstruction and
end-to-end privacy/soundness remain open; production paths are unchanged.

## Checked reducer primitive operations — 2026-09-21

Base `e40ee66066056ef9564df536f31f2ce955e64fa6` plus this changeset.
Exact target `AspisV8R17/UnsignedReducerOps.lean`, SHA-256
`ebe2dfa469ce28c4918e6a5ce6f8d8664d6fc6a107a51bb31c14cc41f48cdcde`,
compiled on the first attempt. Scope `aspis-r17-reducer-ops-r1` in the retained
host workspace; Lean 4.32.0 `-j1 -M1800`, MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64. Exit 0, wall 0.70 seconds, peak RSS 1626228 KiB,
swaps 0, no warnings. No unchanged formal target was replayed.

Seven statements were proved:

- `cast_value`: unsigned casting is reduction modulo the destination width.
- `narrow_exact`: U64-to-U32 casting is exact when the value fits in 32 bits.
- `and_value`: machine-word AND has the corresponding Nat bitwise value.
- `shift_success`: a checked right shift succeeds below the source width and
  returns the exact shifted Nat value.
- `sub_success`: checked subtraction succeeds when the second operand is no
  larger, and returns the exact Nat difference.
- `shift_overflow` and `sub_underflow`: the complementary invalid cases return
  integerOverflow rather than silently yielding a word.

`#print axioms`: and_value uses `[propext, Quot.sound]`; all other six use
`[propext]`. No sorryAx or new assumptions. The retained Step.Init import
supports the original cast attribute without importing full Scalar.Core.

The five SOURCE blocks (cast including its attribute, shift, scalar-count
shift adapter, AND, subtraction) match the pinned runtime source bytes.
The updated checker authenticated all seven complete runtime source files,
matched all five blocks and rejected three in-memory mutations (shift boundary,
subtraction operator and source tag), exit 0. New complete source pins:

- Bitwise.lean: `63e4b1d0906c972fb4fef953d8d8a60410dcf5313261d2583b1170b4a1a5ce29`.
- Casts.lean: `fd709a15b1e66431b788bf2838b79ac662d4c2afd38acbcde078b775c8f1e668`.
- Ops/Sub.lean: `bd6716dad017ce0c0e9cf9084f9223eb5407ece920853ae7675cbe2362dd5e37`.

Boundary remains explicit: these are the real scalar operation definitions,
not yet the full generated reducer. First remaining proposition is successful
composition of both checked folds, exact narrowing and the final conditional
subtraction, with output equal to retained RawReducer.rawReduceU64. The earlier
first/second-fold bounds and residue theorem were inspected for reuse, not
replayed or replaced. Full CM31 reconstruction and the complete repaired
protocol privacy/soundness obligations remain open. No production paths or
negative regressions were changed.

## Checked current CM31 cross fragment — 2026-09-21

Base `6c8d69cea99dc0c2ead0e48ecde4e8bd786407b0` plus this changeset.
Exact target: `AspisV8R17/UnsignedCM31Cross.lean`. Final source SHA-256:
`993faf1f0594828d209c094fa67e54d49a886487100b34d1ffe0be8e506b7354`.
Four new statements compiled in the same cached Lean 4.32.0 host workspace:

- `widen_value`: the retained U32-to-U64 conversion preserves the Nat value.
- `crossOperand_success`: for four canonical M31 words, the two checked U64
  additions and checked multiplication succeed, returning `(a+b)*(c+d)`.
- `generatedCrossFragment_eq`: the literal generated cross subexpression,
  retaining its lifts, temporary names and checked operators, equals that
  operational composition for all inputs, without canonicality premises.
- `generatedCrossFragment_success`: the authenticated generated subexpression
  succeeds with that exact value under the four canonicality bounds.

All four final `#print axioms` results are `[propext, Quot.sound]`, with no
sorryAx or new cryptographic assumptions. The product bound uses symbolic
monotonicity on two factors below 2^32; no large recurrence was normalized.

The unsigned runtime checker now authenticates five marked cross-leaf blocks
(two aliases, conversion, and checked operator instances), as well as the
unchanged 12-block predecessor. The additional complete source pin is
CoreConvertNum.lean SHA-256
`d7bbeaa3cc7422dcad0a52ffc1904a2d11751717a7b5d820d645404e0bf81eaa`.
The cross checker rejected three in-memory runtime-block mutations.
The generated-source checker separately authenticates the two original field
type declarations and the contiguous cross fragment against the already pinned
Types.lean/FunsChunk04.lean; it rejected two generated-block mutations.
Both checks exited 0 against the final compiled source hash. These checks
authenticate marked text, not a complete extraction/refinement pipeline.

All builds used `-j1 -M1800` with MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64; no cap changed and no whole-package replay ran.

| Scope (prefix aspis-r17-unsigned-cross-) | Result | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| r1 | Missing widening lemma and product elaboration mismatch | 1 | 0.82 | 1608468 | 0 |
| r2 | Conversion and composed cross proof compiled | 0 | 0.74 | 1612268 | 0 |
| r3 | Fragment bind lemma namespace / return identity errors | 1 | 0.74 | 1615064 | 0 |
| r4 | Remaining definitional operator equality | 1 | 0.74 | 1614412 | 0 |
| r5 | All four statements compiled, no warnings | 0 | 0.77 | 1626060 | 0 |

Failed elaborations printed sorryAx and were rejected, not treated as evidence.
The final equality closes by a small definitional operator-instance reduction,
after the explicit Result right-unit proof; it is not a large concrete reduction.

Boundary: the extracted fragment starts AFTER m0/m1 and stops BEFORE
M31.reduce_u64. Its wrapper returns the cross operand, not a CM31 result.
First remaining source-specific proposition is correctness and successful
checked execution of the current extracted reducer on this bounded U64 input,
then composition with m0/m1 and both reconstructed coordinates. The full
CM31 multiplication/square, R17 caller, joint privacy and soundness obligations
remain open. No production protocol path or negative regression was changed.

## Authenticated unsigned execution slice — 2026-09-21

Base `fc8a65e5b4519d7355d8afc3f13075e05eb3b18a` plus this changeset.
`AspisV8R17/UnsignedCoreSlice.lean` compiled in the pinned host workspace with
Lean 4.32.0, `-j1 -M1800`, MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0,
TasksMax=64. No full package replay, cap increase or production change ran.

The slice imports Aeneas.Std.Primitives, BvEnumToBitVec and Nat notation only.
Twelve marked blocks, including the unsigned type, bit width, bit-vector
representation, checked constructor and add/mul definitions, match their
original runtime source bytes. `check_r17_unsigned_slice.py` first authenticates
the complete original Core.lean, Ops/Add.lean and Ops/Mul.lean against pinned
SHA-256 hashes. It accepted all 12 blocks and rejected three in-memory mutations.
The final slice SHA-256 is
`dcdca5dd207a676a8c2d604e045ddc9f00868f66cc645841442b26bd50e9ce2c`.
The checker authenticates marked source blocks, not surrounding framing or
complete caller refinement. The slice cannot be imported with full Scalar.Core,
because it intentionally retains the same unsigned declaration names.

New kernel-checked statements:

- `tryMk_success`: below the selected word-width bound, checked construction
  returns an ok word whose value is exactly the supplied Nat.
- `add_success` and `mul_success`: U64 checked addition/multiplication return
  the exact sum/product under their explicit no-overflow bounds.
- `tryMk_overflow`: outside the bound, the constructor returns integerOverflow.

All four `#print axioms` results are exactly `[propext]`; there is no sorryAx
or new hiding assumption. These are operational scalar facts, not a proof of
the CM31 caller, field reduction, privacy or soundness of the repaired protocol.

| Exact target | Scope (prefix aspis-r17-) | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| AspisV8R17/UnsignedCoreSlice, three success theorems | unsigned-slice-r1 | 0 | 0.70 | 1626412 | 0 |
| AspisV8R17/UnsignedCoreSlice, plus overflow theorem and source checker | unsigned-slice-r2 | 0 | 0.76 | 1619332 | 0 |

The preceding whole-Core split was NOT accepted. Its original source hash is
`ceba1982545251f02d6e286abf23d01f4d2a691fe6934149f3a42d4a051af81e`;
only task-owned copies were edited. Replacing four scalar_tac proof uses and
the tactic import reached checking, but the helper imports needed for the full
file again exceeded the cap. A module-mode experiment was incompatible with
the existing non-module cache. Exact failed target: `Aeneas/Std/Scalar/Core`.

| Scope (prefix aspis-r17-scalar-split-) | Result | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| r1 | Missing task overlay cache dependency | 1 | 0.21 | 539560 | 0 |
| r2 | Missing notation/irreducible_def imports | 1 | 0.96 | 1663804 | 0 |
| r3 | Missing order/tactic helpers | 1 | 5.19 | 1802584 | 0 |
| r4 | Interpreter memory exception after helper imports | 134 | 2.42 | 1845168 | 0 |
| r5 | Module/non-module import incompatibility | 1 | 0.20 | 502916 | 0 |
| r6 | Interpreter memory exception with narrower integer-order import | 134 | 2.44 | 1844688 | 0 |

No axioms audit was obtained from these failed candidates. The abandoned local
candidate remains under target/r17-runtime-split; it is not release evidence.
The task overlay used read-only symlink references to cached dependencies;
the original shared runtime source still matches its hash. No new Core.olean
was produced. A read-only link to the original Core.olean was restored in the
overlay, and the runner now refuses to write an olean through a symlink.
The final runner does not allow the abandoned full-Core build target.

First remaining operational proposition: compose the authenticated U32-to-U64
conversion and these checked operations to prove the CURRENT CM31 cross
operand returns `(a+b)*(c+d)` for canonical M31 inputs; then connect the current
reducer and coordinate reconstruction. Joint-view coverage, commitments,
shared-oracle chronology, retries/publication and full soundness remain open.

## Import-floor localization — 2026-09-21

Base `6cb30c9f5bd740822a51474644a1a58d260244b1` plus this changeset.
Three distinct import probes ran with unchanged Lean `-j1 -M1800` and unchanged
4G/6G/zero-swap systemd scope limits in the same pinned cached workspace.
Each source was just the listed import, a diagnostic comment and the listed
`#check`; no new theorem or new axiom was introduced.

| Probe import / check | Scope (prefix aspis-r17-) | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| Lean / Nat | lean-import-r1 | 0 | 0.55 | 1546656 | 0 |
| Aeneas.Std.Primitives / Aeneas.Std.Result | primitives-import-r1 | 0 | 0.54 | 1554096 | 0 |
| Aeneas.Tactic.Solver.ScalarTac.ScalarTac / Nat | scalartac-import-r1 | 134 | 1.81 | 2013936 | 0 |

The first two checks printed their expected types. The third failed with the
same interpreter memory exception before `#check`. Axioms audit: not applicable
to these import-only probes, and no protocol theorem was compiled. The retained
ScalarImportProbe now contains the third, narrower failing import.

Inspection of Scalar/Core.lean found a direct dependency on this tactic module,
which in turn imports RingNF, Linarith via ScalarTac.Core, and tactic extension
modules. Scalar/Core itself uses scalar_tac in four proof locations (lines
996, 1001, 1142 and 1146), in addition to registering scalar tactic attributes.
Thus removing the tactic import from a copied runtime is not a one-line valid
fix: its proof uses and attribute providers must be handled and recompiled,
without changing scalar definitions or weakening their statements. The shared
runtime and compiled cache were not modified. No cap was raised.

This localizes an engineering obstacle; it is not a mathematical obstruction
to the repair and not evidence of either privacy or soundness. The operational
CM31 proof remains pending. A safe next route is a task-owned, authenticated
runtime split separating scalar semantics from tactic-heavy proofs, with
focused recompilation and exact definition checks before adapter use.

## Current extraction authentication and import-memory isolation — 2026-09-21

Base `2c7a4a8d8f6f14856f1e1d4078c69a35969e0747` plus this changeset.
No new arithmetic theorem compiled in this checkpoint. The current-source
checked-arithmetic adapter remains an uncompiled local draft, not release evidence.

`CurrentFieldSlice.lean` retains 11 generated declarations and their attributes
byte-for-byte from the cached current caller. The read-only checker authenticates
both complete input files before comparing the declaration inventory and bodies:

- Types.lean: `02c93204cbcaa6f5389fed89b9e67074536c6375f990a4504bba297c7780138b`.
- FunsChunk04.lean: `e79e0726e1a58ebfe3701b83f4339ca52b042e46cae833d573df3190c4bd0c21`.
- Narrow-import slice: `a012e37dfa23b84471e5571c73c7c758f774bb0a03aa06ca25f6f29e5e97667e`.

Checker execution with `--self-test` exited 0: 11 declarations matched;
four in-memory mutations (constant, attribute, missing name, extra declaration)
were rejected. This authenticates a source projection, NOT source refinement,
compiled kernel evidence, or an R17 caller theorem. Imports and namespace framing
are outside the byte comparison. Do not import this slice alongside the complete
caller: it deliberately retains the same declaration names.

All following attempts ran on nuc.local in separate user systemd scopes, with
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64, Lean 4.32.0,
`-j1 -M1800`, and the existing pinned mathlib/Aeneas caches. The task directory
was `/home/dombarker/project-offloads/aspis-r17-extracted-cm31.JXBWPZ`.
Time/RSS/swap are GNU time measurements. Every attempt terminated by signal 6
with wrapper exit 134 (the time footer's exit 0 is not a successful compilation).

| Target / change | Wall seconds | Peak RSS KiB | Swaps | Axioms audit |
| --- | ---: | ---: | ---: | --- |
| ExtractedCM31Operands, full caller import, scope cm31-operands-r1 | 3.36 | 2189380 | 0 | Not reached |
| CurrentFieldSlice, Aeneas.Std import, scope cm31-slice-r2 | 1.76 | 2184892 | 0 | Not reached |
| CurrentFieldSlice, narrowed scalar imports, scope cm31-slice-r3 | 1.74 | 2165128 | 0 | Not reached |
| ScalarImportProbe, only Aeneas.Std.Scalar.Core, scope scalar-import-r1 | 1.89 | 2029900 | 0 | No theorem; check not reached |

The first scope names above have prefix `aspis-r17-`; the last is
`aspis-r17-scalar-import-r1`. Each failed with Lean's interpreter memory
exception, not a cgroup OOM. The minimal probe contains only one import and
`#check UScalar`, isolating the obstruction below our arithmetic proof bodies.
No unchanged failed job was rerun with a larger cap; no whole-package build ran.
The narrowed imports did not solve this cached runtime's import-memory floor.

Next engineering step: inspect/reduce the cached Aeneas scalar import closure
under the resource policy before retrying the adapter. First mathematical
obligation remains successful checked execution of the CURRENT CM31 lazy
cross operand with value `(a+b)*(c+d)`, followed by the actual reducer and
coordinate reconstruction. The retained Nat/ZMod theorem does not itself
establish this operational statement. Full privacy and soundness stay open.

## Arithmetic source reuse audit and current CM31 deltas — 2026-09-21

Base `841909cbf881fb07a636bf267ae61fbcd89b7d55` plus this changeset.
Read-only inspection located the cached V7 Aeneas caller workspace on
nuc.local at project-offloads/aspis-v7-aeneas-source-unblock-20260830,
including staged-current-normalized-statement-owned-twohelpers-r19 and its
CurrentCallerAudit. No extraction, replay, deployment or wallet action ran.
Its input field.rs, its normalized field.rs, the current privacy worktree
and v19 staged field.rs all have SHA-256
`5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8`.
The caller audit prints translated definitions and split-helper equalities;
it does not prove the new R17 mask caller merely by existing.

The tracked component-b-weight-at/arithmetic-lean432 README supersedes the
older V5 formula-seam commentary about a general 4.31/4.32 gap: it reports
a 4.32 replay of the source-authentic arithmetic proofs. HOWEVER its pinned
field source is the older blob `a28ff94de05265102ca819849805a7f73c675800`,
SHA-256 `dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836`.
Comparing that blob to current field.rs finds relevant body changes in
M31::half (low-31 rotate), CM31::mul (unreduced cross-term sums), and
CM31::square (unreduced real-coordinate factors), plus other helpers.
An unchanged QM31 outer body does not erase changed CM31 dependencies.

Manifest authentication was attempted, not assumed:

- The 42-entry SOURCE_MANIFEST.sha256 itself matches
  `7832fe9d7ed7ce56aedc2c568d40354330790af6197720edb58a2f6b0e438a01`.
- The privacy-worktree copy lacks SumProductsComponentLoop.lean,
  SumProductsFullCorrespondence.lean and SumProductsLoop.lean.
- The main workspace has those three files with their expected manifest
  hashes, but its complete check still fails on HalfProof.lean.
- Both copies' HalfProof.lean hash is
  `7f1ee2400114870347fc3b90eda801fcad63197f14c10f8cab06a4eca0a79d6d`,
  whereas the manifest requires
  `d7c073dd5b1740aad11cf7a949c43399f894f5e11c0ffa3fafd8bcd8b4da9fc0`.

Neither copy is accepted as a fully authenticated release replay. No files
were overwritten, copied into the branch or repinned to hide these failures.
The retained LineNorm.lean separately contains the current rotate-half
mathematics; it was inspected, not recompiled or promoted to an extracted
current-source theorem in this turn.

New RawReducer.lean is a narrow replay of retained proof bodies from
V5M31RawMulReduction.lean (lines 55–232) and the addition proofs in
V5ComponentCQM31RustFormulaSeam.lean (lines 160–193). Only the namespace,
imports and minimal aliases change. The full cached reducer import pulled
in the deployment/sampler aggregate and hit the UNCHANGED -M1800 cap.
The replacement avoids those imports and rechecks the literal bit-fold
reducer, canonicality, residue and canonical multiplication/addition facts.

SourceLazyCM31.lean proves the actual new raw cross and square-real factors
do not overflow u64 (and square subtraction cannot underflow), then reuses
that reducer to establish canonical outputs and exact residues. For the
cross term it proves equality to the older reduce-each-sum implementation
as a canonical WORD, not only a congruence. This supplies the mathematical
current-source delta, not equality of a freshly extracted Rust definition.

First remaining source-specific proposition: connect the current extracted
CM31 optimized bodies to these raw graphs and compose them with the retained
QM31 operation correspondences in an authenticated, compatible extraction
universe; then link the R17 mask caller to its mutation model. Existing
source/proof pin failures remain visible. No global privacy, soundness,
source sampler or full-transcript conclusion follows from this delta.

Focused cached `/Users/dominic/ZK/AspisFormal` commands use `lake env lean
-j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, timed with `/usr/bin/time -l`:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| SourceLazyCM31, full cached reducer import | 134 | 45.04 | 4317741056 | 0 |
| RawReducer, narrowed retained proof replay | 0 | 8.84 | 1630748672 | 0 |
| SourceLazyCM31, explicit ModEq conversion still missing | 1 | 2.30 | 1613250560 | 0 |
| SourceLazyCM31, explicit residue equality | 0 | 3.35 | 1630601216 | 0 |
| Privacy-worktree manifest check | 1 | 0.03 | 7405568 | 0 |
| Main-workspace manifest check | 1 | 0.01 | 7045120 | 0 |

The memory failure was an import/dependency problem, not permission to raise
the cap. All nine final axioms audits use only subsets of propext,
Classical.choice and Quot.sound, no sorryAx, and both final leaves have no
warnings. No production source, unrelated work, negative regression or pin
was changed. No full manifest compilation or unchanged runtime suite ran.

## Reverse table writes and noninterference — 2026-09-21

Base `2c038f925ba5500abc4aa1362dc07f5dca5d51fb` plus this changeset.
`ConsecutiveWrites.lean` proves sequential Function.update writes preserve
every outside entry, write the intended inside entry, compose by list append,
and commute for adjacent disjoint blocks. These facts are symbolic in lengths;
the proof never normalizes a concrete 271-write chain.

`MaskWeightWrites.lean` models the source's actual high-round-to-low-round
chronology, writing each literal inner power-loop block and then writing
the final carry scale at zero. The table equals writing the proved flat mask
weights, entry by entry, for ANY initial table. Thus initialization values
cannot leak into an unfilled coordinate in this model. The model leaves
entries above 270 unchanged. A separate arithmetic lemma proves that every
1+27*r+i address (r<10, i<27) is nonzero and below 271; another proves those
addresses are injective. The final source_written_mask_pairing consumes this
mutating-table model in the already-proved mixing/mask functional identity.

The previous recursive-block-to-mutation-model gap is now discharged.
This remains a mathematical mutation model, not an imported Charon/Aeneas
translation of the pinned Rust function. No equality between extracted
Rust code and this model is silently assumed or claimed proved.

Read the retained V5ComponentCQM31RustFormulaSeam.lean and
V5M31RawMulReduction.lean before considering field instantiation. The former
explicitly states that executable-function equalities remain named premises
(including RustCanonicalM31PrimitivesMatch), and documents a historical
cross-toolchain raw-add seam. The latter proves the mathematical literal
two-fold M31 reduction graph and canonical bounds. Their existence alone
does not close the present Rust execution/field boundary. Existing exact
tower and raw-operation work should be reused, not replaced with a new
field assumption or another cold dependency replay.

First remaining source-specific proposition: an exact pinned Rust execution
refinement, or a composed source-locked semantics proof, connects mask_weights
array mutation, its caller's point-array conversion and QM31 operations to
sourceMaskTable and the exact tower. Point-construction, concrete order,
commitment/image/fold/extraction and adaptive-challenge gates remain open.
Joint privacy coverage and full-transcript simulation are not implied by
this opening-functional result.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`, per-leaf command
`lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, measured by `/usr/bin/time -l`:

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| ConsecutiveWrites | 0 | 7.51 | 1214808064 | 0 |
| MaskWeightWrites, dependent bridge | 0 | 8.98 | 1804025856 | 0 |

All twelve #print axioms outputs use only subsets of propext,
Classical.choice and Quot.sound, with no sorryAx. ConsecutiveWrites emits one
unused simp-argument warning; MaskWeightWrites has no warnings. No production
path, source pin or negative regression changed. No full manifest, cold
dependency build, Aeneas replay or unchanged runtime suite was launched.

## Structured-mask weights, carry and source slices — 2026-09-21

Base `42596fba8798302aaf5290d28a0303b9a7f27611` plus this changeset.
Three new leaves discharge the earlier flat-coordinate algebraic gap:

- `MaskWeightBlocks.lean` proves the scaled 27-entry round-block dot
  product, matching list lengths, reverse-round block construction and
  carry scale half^r. The complete carry-plus-block dot product equals the
  literal mask loop and, at half=1/2, the retained structuredMask.
- `MaskWeightVector.lean` proves the literal inner power-weight recurrence
  and supplies a length-checked Fin 271 interface for the ten 27-entry
  blocks plus carry. No truncated zip or omitted coordinate enters it.
- `MaskSourceSlices.lean` proves that reads starting at 1 and advancing
  by 27 flatten to exactly the original 271 coordinates including carry
  at zero. The final source_mask_weights_pairing discharges the intermediate
  slices equality premise for the SAME computed Horner outputs. Its final
  source_original_mask_weight_dot composes the mask evaluation with G's
  retained point-1, point-2 and inactive-sum terms.

The final pairing is not conditional on a new hiding/coverage premise.
It is deterministic source-shaped algebra for arbitrary m and challenge
coordinates. In particular, no source coin is resampled and the 271 mixed
coordinates are not asserted independent or uniform. The intermediate
mixed_mask_weights_pairing still documents its slices premise; the final
MaskSourceSlices theorem actually proves and instantiates that premise.

Rechecked local and v19 staged r17_structured_g.rs, identical SHA-256
`147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6`.
The inner power recurrence, source slice offsets, reverse chronology and
carry contribution are now represented and proved. The outer weight-table
construction is a recursive block model: equality to every Rust mutable
array write has NOT been claimed as an extracted execution theorem.

First remaining source-specific proposition: the pinned Rust mask_weights
array writes, field operations and point-array conversion refine these
flat blocks and the composed opening functional. The point-construction
API, concrete field representation, fixed inventory/order and full verifier
acceptance/extraction still need their source connections. This does not
discharge commitment binding, high-tail image validity, folds/final openings,
adaptive challenge losses, joint legal C1/H1/G coverage or full privacy.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`; per leaf command
`lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, measured by `/usr/bin/time -l`:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| MaskWeightBlocks | 0 | 10.49 | 1705148416 | 0 |
| MaskWeightVector | 0 | 8.77 | 1795915776 | 0 |
| MaskSourceSlices, initial distribution/rewrite failure | 1 | 6.42 | 1790836736 | 0 |
| MaskSourceSlices, side-restricted rewrite; congr recursion failure | 1 | 5.88 | 1773158400 | 0 |
| MaskSourceSlices, explicit function equality | 0 | 3.93 | 1801912320 | 0 |
| MaskSourceSlices, added original-weight composition | 0 | 1.94 | 1802960896 | 0 |

Seventeen final #print axioms declarations contain only subsets of propext,
Classical.choice and Quot.sound; no sorryAx. Final leaves have respectively
one, two, and three unused-instance/simp-argument warnings. The failed
drafts were not evidence. Their replacement uses symbolic distributivity,
restricted rewriting and function extensionality, not increased limits or
normalization of the 270-entry list. No production changes, removed negative
regressions, full manifest replay or unchanged runtime replay occurred.

## Original opening weights and mixing transpose — 2026-09-21

Base `8a58262abc8429cefe370cccbc9e4f1f9e0f2a97` plus this changeset.
`SourceOriginalWeights.lean` models the length-10 multilinear component's
multiply-accumulator, with the exact big-endian bit-position expression
`(index >> (9-coordinate)) & 1`. It proves the product form, then models the
original_weights component list, inactive-row addition, and optional G term.
The ordinary branch has all three point components with scales kappa,
kappa^2, kappa^3. The structured branch replaces ONLY the first component
with kappa times the supplied G-weight vector. The other two point components
and inactive-sum claim remain. A composed theorem feeds this exact model into
the retained transport/chord/residual opening identity for arbitrary q.

The three length-10 point arrays are explicit inputs. The point functional
is explicitly the dot product against the big-endian basis; this is not yet
a refinement of every existing EvaluationClaim or point-construction API.
The source v6_statement_points constructs z, a carry-propagated successor,
and the point with coordinates 7 and 6 flipped; the model does not silently
substitute independent points or assume those constructions have been proved.

`SourceMixingWeights.lean` proves the power-row generation recurrence, the
nested weighted-row accumulation formula, and its dot-product identity with
the SAME 271 reverse-Horner outputs of the original 1024-entry vector.
Its final theorem instantiates the structured original-weight functional
with this mixing transpose, retaining the other two point functionals and
the inactive sum. No fresh mask, uniform prefix law or new hiding assumption
is introduced. The 271 coin weights remain explicit inputs.

First remaining source-specific proposition: the actual reverse-round loop
that writes coin_weights[0] and the ten 27-entry slices at 1+27*r produces
the linear functional for the retained mask_eval, including the carry scale,
zero-boundary coefficients, and complete round chronology. Then connect the
point construction and Rust array/field operations to the model, rather than
treating this source-shaped algebra as execution extraction. Source joint
coverage, commitment extraction, image/fold/final consistency, shared-oracle
challenge bounds and full privacy/soundness losses remain separate open gates.

Inspected source pins (local and v19 staged core files identical):

- sumcheck.rs, add_multilinear and weight_at:
  `7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead`.
- v6_transcript.rs, v6_statement_points:
  `48275a37053ce5d33c7ec61caf6301863666f45a1e388c2c64bdb856708764cf`.
- r17_structured_g.rs, mixing_row/mixed_coins/mask_weights:
  `147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6`.

The two modules were compiled smallest-first in cached
`/Users/dominic/ZK/AspisFormal`, using `lake env lean -j1 -M1800 -R
<research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, measured by `/usr/bin/time -l`:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| SourceOriginalWeights | 0 | 8.14 | 1480966144 | 0 |
| SourceMixingWeights, broad simp/CharP recursion failure | 1 | 12.08 | 1767047168 | 0 |
| SourceMixingWeights, restricted simp; remaining composition | 1 | 7.03 | 1781071872 | 0 |
| SourceMixingWeights, explicit Function.comp_def and integrated bridge | 0 | 2.16 | 1803141120 | 0 |

The fix was explicit symbolic rewriting, not a recursion/memory-cap increase.
All ten final #print axioms outputs contain only subsets of propext,
Classical.choice and Quot.sound, with no sorryAx. Both final leaves have no
warnings. Failed drafts were not accepted as evidence. No production paths,
negative regressions, full manifests or unchanged runtime suites were changed
or replayed.

## Composed source-shaped opening identity — 2026-09-21

Base `aba46950365f4b90214027d1e1441355b0a61b3f` plus this changeset.
Four focused leaves now connect the previously separate algebraic steps:

- `ChordDual.lean`: finite dot-product padding lemmas and the full-width
  even/odd chord pairing. All 514 positions per output lane remain present.
  The single-scatter extra coordinate is eliminated by its proved support
  bound, while the double scatter retains the complete intermediate vector.
- `SourceChordTranspose.lean`: parity-sum/interleaving identities and the
  source-shaped 1024-coordinate chord transpose, with both weight lanes
  zero-extended from 512 to 514. Its pairing holds for arbitrary q.
- `SourceOpeningResidual.lean`: literal sequential updates at 1023, 1022,
  1021, then the separate ordinary and structured-G channel pairing.
- `TransportedOpening.lean`: composes the result with TransportDual's
  arbitrary-coefficient identity, converting between finite row indices and
  the natural-indexed source-loop model.

The final theorem `transported_source_opening_pairing` states that the
computed quotient-weight dot product is the original-weight dot product on
inverseTransport(sourceChord(q)), PLUS the actual channel residual terms.
There is no honest-generation, legal-mask or residual-zero premise on q.
The theorem parameterizes the public order and inactive set; exact source
inventory correspondence remains required.

The compiled two-channel formula retains precisely:

```
tau   * qR[1023]
+ tau^2 * (b*qR[1022] - c*qR[1021])
+ tau^3 * qG[1023]
+ tau^4 * (b*qG[1022] - c*qG[1021]).
```

These are not silently set to zero. The combined image check still needs
the ordinary/carried-error term and its degree-4 accounting from the retained
two-channel argument. The pairing is deterministic algebra, not a root-count
or Fiat--Shamir distribution theorem.

Crucially, weight zero-padding proves a pairing with the retained low 1024
forward coefficients even if the four high output coefficients are nonzero.
This does not prove high-tail-zero acceptance or that a malicious quotient
lies in the required image. The audit's high-tail assertion is not inherited
as an assumption. That distinction preserves the separate image soundness gate.

Rechecked local r16_basis_transport.rs SHA-256
`36466ca34b091ee2e058deb3c66d1306164c0b6869719586175ddefa87a37dcf`;
local and v19 staged r17_opening_weights.rs are identical at SHA-256
`bc0068b47eba5f871fac7ff809aad79bff738357ead553fa2ded7fd579428fec`.
This is a mathematical model of that source shape, not an extracted Rust
execution proof. Original weights, the source field embedding/word operations,
array reads/writes and the concrete fixed inventory remain source obligations.

First remaining source-specific proposition: `original_weights` and its
WeightAccumulator/structured-mask materialization, together with the actual
field/array implementation of the composed pipeline, realize this identity
for both channels and arbitrary extracted coefficients. Commitment extraction,
image validity, all folds/final openings, adaptive challenges and explicit
soundness loss still require their own proofs. The joint legal C1/H1/G
coverage and full-transcript privacy gates are unchanged, not discharged.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`; each leaf compiled
with `lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, measured with `/usr/bin/time -l`:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| ChordDual, initial partial-application simplification | 1 | 8.55 | 1427341312 | 0 |
| ChordDual, explicit unfolding of partial applications | 0 | 1.90 | 1445609472 | 0 |
| SourceChordTranspose | 0 | 1.81 | 1444331520 | 0 |
| SourceOpeningResidual | 0 | 2.99 | 1444249600 | 0 |
| TransportedOpening, dependent composed bridge | 0 | 2.61 | 1468203008 | 0 |

Twelve final #print axioms declarations use only subsets of propext,
Classical.choice and Quot.sound. No sorryAx. SourceChordTranspose emits two
unused section-instance warnings, SourceOpeningResidual one unused simp
argument warning; the final bridge has no warnings. The failed initial draft
was not proof evidence. No cap increase, production change, full manifest
replay, or unchanged runtime regression occurred.

## Bounded source scatter/gather adjoint — 2026-09-21

Base `3a53c79a5003755c885fd6b87e98b9d046a9d51d` plus this changeset.
`AspisV8R17/ScatterDual.lean` proves the finite dot-product identity for
the retained scatter edge lists and their gather operation. Input and output
index bounds are explicit. It identifies the gather of sourceEdges with
the weightedIndexLoop read sum, and instantiates the adjoint at any retained
bounded schedule. This uses the existing index certificate, not another
enumeration of dense field matrices.

`AspisV8R17/SourceGatherLoop.lean` models the accumulator in the verifier's
xt: on each set bit it clears the bit, multiplies scale by half, and adds
the weighted read; the final read sets the first clear bit. It proves this
loop equals the weighted read sum. The retained certificates discharge
termination at all inputs below 512 and 513. The double-scatter adjoint
preserves the actual 512 -> 513 -> 514 forward sizes and reverses them for
the gather; the 513 intermediate coordinates are not discarded.

Inspected local tools and identical v19 staged files:

- r17_opening_weights.rs SHA-256
  `bc0068b47eba5f871fac7ff809aad79bff738357ead553fa2ded7fd579428fec`.
- r17_coupled_audit.rs SHA-256
  `74f6ec7eff5c747656168dabd1cefd9cb7326fc29c9fd6ccf2d46a10e944c690`.

The opening code pads weights from 1024 to 1028, splits even/odd lanes,
gathers to 513 and then 512, and recombines 1024 weights. The audit's forward
chord computes 1028 coefficients, asserts its high tail zero, then truncates.
The new identities hold for arbitrary inputs at the stated dimensions;
they do NOT assume or establish that high-tail assertion. In particular,
an honest diagnostic assertion is not a malicious-prover image proof.

Next exact proposition: combine these adjoints with the retained
finiteChordEven/finiteChordOdd equations, preserving parity splitting and
zero-extended weights, to prove the entire chord_transpose pairing. Then
compose with TransportDual and the two distinct residual-weight formulas.
Word-level Rust/field refinement, original-weight materialization, extraction,
challenge bounds and the joint privacy obligations remain open. No new hiding
or adjoint assumption was introduced.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`; command for each
leaf: `lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, timed by `/usr/bin/time -l`.

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| ScatterDual, initial map-composition simplification | 1 | 10.18 | 1430159360 | 0 |
| ScatterDual, explicit Function.comp_def | 0 | 4.62 | 1444233216 | 0 |
| SourceGatherLoop, loop identities | 0 | 1.72 | 1445806080 | 0 |
| SourceGatherLoop, added double-scatter bridge | 0 | 3.32 | 1447788544 | 0 |

Three ScatterDual and five final SourceGatherLoop #print axioms results use
only subsets of propext, Classical.choice, Quot.sound, with no sorryAx.
The failed draft was not accepted evidence. No production changes, cap
increases, full-manifest replay or unchanged runtime suites were performed.

## Universal inverse-dual algebra — 2026-09-21

Base `7048dd6bb844a46ba49d5f224800720e915da3be` plus this changeset.
New `lean/AspisV8R16/TransportDual.lean` proves `inverseTransport_dot`:
for EVERY coefficient vector c and weight vector w over a commutative ring,
the dot product of w with inverseTransport(c) equals the dot product of the
explicit transported weights with c. There is no honest-generation,
balanced-mask, or legal-witness premise. The forward corollary uses the
retained inverse theorem and pivot membership. This closes the universal
model-level algebraic identity, not its exact-source refinement.

The weight formula subtracts w(pivot) exactly at rows in inactive.erase(pivot),
then permutes by order. This is the predicate `r != PIVOT && inactive[r]`
in the inspected Rust `Transport::dual`. The generic permutation model still
requires source inventory correspondence; the Rust forward/inverse loops
specifically rely on their constructor leaving PIVOT in the final slot.

Inspected identical local tool and v19 staged `r16_basis_transport.rs`:
SHA-256 `36466ca34b091ee2e058deb3c66d1306164c0b6869719586175ddefa87a37dcf`.
Inspected staged `r17_opening_weights.rs`:
SHA-256 `bc0068b47eba5f871fac7ff809aad79bff738357ead553fa2ded7fd579428fec`.
Its quotient_weights applies this dual to original_weights, then the chord
transpose, then the separate ordinary/structured image residual weights.
The new theorem does NOT prove that chord transpose, original-weight
materialization, residual checks, Rust field operations or extraction.

Focused cached compilation in `/Users/dominic/ZK/AspisFormal`, using
`lake env lean -j1 -M1800 -R <research>/lean -o <r16-cache>/TransportDual.olean
<research>/lean/AspisV8R16/TransportDual.lean`, measured with `/usr/bin/time -l`:

| Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial sum rewrite | 1 | 8.70 | 1424359424 | 0 |
| Pointwise rewrite; remaining finite-set equality | 1 | 5.18 | 1423835136 | 0 |
| Explicit finite-set extensionality | 0 | 3.19 | 1437286400 | 0 |

Both final #print axioms results contain only propext, Classical.choice,
Quot.sound; no sorryAx. Failed attempts were not accepted proof evidence.
No resource cap increase, production change, unchanged runtime regression,
or full-manifest replay was performed.

First remaining soundness-specific proposition: the exact staged opening
weight pipeline, including chord transpose and distinct channel residuals,
computes the required functional on arbitrary extracted coefficient vectors.
Its Rust/field refinement and subsequent binding, extraction, adaptive
challenge and loss-accounting gates remain open. Joint legal C1/H1/G privacy
coverage remains a separate obligation; this soundness lemma does not close it.

Date: 2026-09-20. Base privacy revision `1d77761f`.

The raw C1 privacy separator is not evidence of a soundness break. However,
R16 changes the encoding/verification relation and must not inherit a
soundness verdict solely because honest fixtures pass.

## What follows from the reversible map

At the algebraic model level, `transportEquiv` supplies both inverses of T.
For any encoder E on the complete message space, `range(E ∘ T) = range(E)`:
one inclusion applies E to Tm, the other chooses `T⁻¹m`. Thus this basis
change does not itself enlarge the ambient codebook or change the set of
codewords on which distance/list bounds are stated. This is a mathematical
consequence, not a compiled end-to-end soundness theorem or a statement
that all such messages satisfy the payment relation.

Original semantic messages and constraints must continue to refer to
`m = T⁻¹c`, where c is the extracted encoded coefficient vector. The
required functional identity is `dot(w,m) = dot(T⁻ᵀw,c)`. It must hold for
arbitrary maliciously supplied c, not merely honestly produced witnesses.
M31/QM31 basis tests and the staged dense differential checks exercise this
identity; its exact-source universal formal refinement remains open.

## Required source gates, none waived

| Gate | Checked evidence | Remaining proposition |
| --- | --- | --- |
| Fixed public transform | Source-derived immutable order; legal-cell assertions; inverse tests; generic Lean equivalence | Concrete Rust loops/field operations refine that equivalence |
| Joint commitment extraction | Both C1 and C2 use the same T; ordinary encoder and Merkle verification retained | Binding/extraction for the new profile yields a coherent c for every batched column |
| Original semantic relation | Ten-round semantic code remains on original rows; honest public-byte verification passes | Accepted point claims equal evaluations of T⁻¹c except for an explicitly bounded bad event |
| Functional transport | Inverse dual precedes chord transpose; dense and entrywise calculations agree in controls | Universal exact-source dual/chord identity and batching bounds |
| Quotient/image condition | Existing top-coefficient checks and verifier image terminal retained | Extracted quotient satisfying new functional checks corresponds to the same encoded polynomial, including all exceptional OOD cases |
| Final values/openings | Existing authenticated openings and structured/dense outcome comparison retained | Full extraction and consistency theorem through all folds and Final256 |
| Fiat–Shamir chronology | Distinct R16 profile absorbed by prover and verifier; exact map included in descriptor | Source oracle transcript, challenge distribution, query budget and soundness loss for this profile |
| Invalid proofs | Both exercised witnesses accept; byte-corruption/truncation controls reject | Quantified malicious-prover soundness, not a finite mutation sample |

The first soundness-specific source theorem is the universal transported
functional identity for the exact verifier weights, composed with the
existing chord transpose and original point/inactive claims. The wider
commitment/extraction and Fiat–Shamir obligations still need their own
premises and loss accounting. The new profile changes transcript bytes;
old challenges or old proof bytes cannot be assumed identical.

There is no current full soundness-preservation claim, no full privacy
claim, and no release/deployment approval. Closing either ledger alone is
insufficient for the user's full-repair goal.

## R17 structured-G integration boundary (2026-09-20)

The R17 prototype would require a G-specific opening functional. The R16
source instead proves one functional of a single gamma-batched message.
`R17_MIXED_MASK_BOUNDARY.md` records source hashes, a compiled impossibility
lemma for unequal functionals on a single combined input, and an executable
negative regression. Changing a common inverse-dual weight cannot repair
that mismatch. A distinct opening argument (such as the specified, still
unimplemented two-channel route) must be soundness-checked; the old verifier
must not be patched to accept unmatched claims. This is not a demonstrated
soundness break in the unchanged protocol.

The next R17 step is now an arithmetic prototype, documented in
`R17_TWO_CHANNEL_OPENING.md`. Its two functionals remain distinct through
both quotient channels, four image residuals and four relation rounds.
The compiled root-count bounds must include the ordinary/carried error:
degree 4 for the combined image check and degree 44 for the combined
query check. The smaller image-only degree-3 bound is not the whole gate's
soundness bound. Uniform challenge, source chronology, binding/extraction
and adversarial query-budget premises remain open; no end-to-end loss or
soundness-preservation claim follows from the prototype.

The subsequent `R17_SOURCE_INTEGRATION.md` records a matched staged host
implementation and honest/negative runtime controls. This advances source
implementation, not the universal extraction/refinement or Fiat--Shamir
soundness gates above. Production protocol paths remain unchanged.
