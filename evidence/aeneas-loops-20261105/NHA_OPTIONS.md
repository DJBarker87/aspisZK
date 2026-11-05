# NHA non-invasive routes — in progress

All routes retain the exact pinned binary. No shared tool or frozen shipped source is edited.

## Option inventory and tested settings

Pinned help is committed as NHA_aeneas_help.txt and NHA_charon_cargo_help.txt. Aeneas exposes -strict-joins, -eval-drops, -loops-to-rec and -loops-no-rec; there is no exposed switch to disable marker invariants or repair abstraction identity. Source inspection shows the loop-to-rec/no-rec settings operate in PureMicroPassesLoops, AFTER the failing symbolic interpreter. They are not an alternate symbolic loop algorithm. Disabling assertions or swallowing a failed join is not a valid option.

| Shape | Retained input default | strict joins + loops-no-rec | eval-drops + loops-to-rec |
|---|---|---|---|
| NGA field reference (not actual frozen body) | E001, exit2, marker assertion2731 | E004, exit2, same assertion | E007 uses actual frozen body instead: same2731 assertion |
| Actual queries | E002, exit2, Map.find1991 | E005, exit2, same Map.find | E008, exit2, same Map.find |
| Actual prepared_claim | E003, exit2, Map.find1991 | E006, exit2, same Map.find | E009, exit2, same Map.find |

Exact commands/metrics are in each receipt. No timeout, memory kill, or unchanged retry occurred.

## Charon-only options / attributes

The pinned Charon help offers built/promoted/elaborated/optimized MIR, opacity/include selection, and --start-from-attribute (root selection). No documented option outlines a Rust loop or selectively changes borrow abstraction joining. ULLBC is not the structured input needed by Aeneas. The present aeneas preset already performs loop reconstruction and index/operation conversion. Switching MIR can change the extraction interface and is not equivalent to a join fix. No shipped attributes are allowed. --start-from-attribute only selects roots already annotated, so cannot create the missing helper without a source change. Scratch roots use command-line --start-from; source attributes are unnecessary. No unrecorded attribute experiment is claimed.

## Outlining specification

NHA_prepare_outline.py reconstructs private frozen dependencies from Git4bb3b3f5 and records every input hash in NHA_SCRATCH_INPUTS.json. Only two module registrations and NHA_ modules differ in the final scratch workspace. The initial reduced-member manifest was rejected by cargo --locked (C001); it was replaced with the exact frozen workspace and all member/path manifests before any new LLBC was accepted. Original function bodies are preserved byte-for-byte, with wrapper names/visibility changed; original .rs.txt cuts are committed. The OUTLINED copies are deliberately different, and never described as byte-identical frozen functions.

Field: preserve exact cache prelude; lift the channel loop into NHA_channels; outer component loop calls it and threads sums. Actual frozen original is separately extracted to correct NHA-F1.

Queries: preserve QueryScan, scan, finish, query_words and block_rank helper bodies; move the eight-block loop into NHA_blocks, returning (scan,state) before the original fallible finish. There is no nested loop syntactically in queries_from_pairs: its inner word loop is already in QueryScan::scan. This is caller/helper fission, not an invented inner loop.

Claim: lift the29-lane dot loop into NHA_dot with exact scalar selection/push/map_err/finish, returning Result<E,Error>. Also lift the final7-term weighted sum and ordered trace calls into NHA_sum. The earlier read-only S1-CACHED-CLAIM-FISSION-PROGRESS-20261020.md records that inner-only outlining still failed on the final sum; hence the new attempt tests both fissions. It is not a repeated known failing inner-only shape.

Any successful outlined emission requires the ruling(ah) actual frozen function/reference contract, exact modifies, matched control and reviewed transcription. There is no emitted original-body theorem to which Lean can equate the outlined copy. No equality or native bridge is claimed here. Kani is forbidden by this job's0 budget.

Own-input exclusions: S005 failed during local reconstruction of a binary optional fixture, before a host command; the source filter now copies Rust/Cargo inputs for optional path crates. C001 refused a lock update on the reduced workspace, with lock unchanged. C005 reached the compiler but exposed an omitted private Rank alias in the query scratch module; the exact frozen alias was added. These are reconstruction errors, not extractor failures or lock drift.

## Outlining results (incremental)

Field: C002 succeeds with frozen lock unchanged; E010 fails again at InterpBorrows.ml:2731, now inside the isolated channel helper. Outlining only the nested loop does not eliminate the marker-bearing shared loan on nested array indexing. No Lean is emitted. A future reference may instead pass single selected rows into the helper, but that changes its interface beyond syntactic loop lifting and still needs the(ah) frozen-body link.

Queries: C003 succeeds with frozen lock unchanged. E011 succeeds (0.549674s,82016KiB RSS,swap0) and emits Types/Funs plus external templates. This is an outlined REFERENCE emission, not the failed original. Raw Types/Funs are retained byte-identically in NHA_emitted/queries_from_pairs. The external templates contain Aeneas-generated axiom placeholders and are evidence only: they are not compiled or admitted. Compilation will use only concrete reused operation definitions from the coherent NGK environment, with their native std-operation boundaries retained.

Claim: C004 initially failed on a missing frozen statement include (glue_gen.rs), then C007 succeeded after reconstructing that file, with frozen Cargo.lock unchanged. E012 still fails at collapse_ctx_following_sequence:1991 despite outlining BOTH the dot loop and final sum. The old S1 precedent does not establish this current frozen/pinned-tool shape. No Lean emitted; no unchanged rerun.

Extraction budget is exhausted:12/12 actual Aeneas runs (including the additional actual-field reproduction),0 Kani. Compilation of the successful query reference continues independently.

Compilation L005 exposed a generated metadata collision: the discriminant macro in the fresh error enum registers global instDiscriminantQuerySampleErrorIsize, already owned by coherent ExtractedOpeningQueriesModel. The raw emission is preserved unchanged. The compile-only Types copy omits exactly the unused @[discriminant isize] attribute (NHA_GENERATED_ADAPTATION.diff); the error type, all constructors, and every function body stay unchanged. No emitted function casts this enum or consumes that instance. This is a disclosed import/metadata adaptation, not a native equality proof or patched extraction. Types and its dependents are rebuilt under the changed dependency, without limit increases.

Query compile result: L003/L008/L009/L010 compile external carrier import, adapted Types, concrete external aliases and unchanged Funs, respectively. L007 co-imports all of it with NGK_COMBINED_IMPORT and the deployed headline: exit0,3.190129s,5936124KiB RSS,swap0. Printed query, block-loop, scanner and headline axioms are exactly[propext,Classical.choice,Quot.sound]. No theorem is introduced, and no native correspondence or cohort equality is inferred from compilation. L001 was excluded before launch because an assumed shared lakefile was absent; the client now creates its own minimal Lake manifest. The emitted-function library objects selected by LEAN_PATH are hash-pinned in every compile receipt.
