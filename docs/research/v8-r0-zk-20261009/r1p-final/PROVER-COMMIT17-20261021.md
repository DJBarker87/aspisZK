# Prover commitment part 17 — ordered traversal and source boundaries

Base `47ccfa22c`; branch `codex/cx-prover-commit17-20261021`.

## Scope

The requested target is the shipped prover's `RustProverRefinement`, for both
real and ideal runs. Existing part-16 evidence is reused only in its original
scope. Its four accepted checks are one-value compaction, one-value rejection,
one-value expansion and node-slot offsets; they are not four full sections of
the proof serializer. No timed-out ordered-Vec harness will be rerun.

The concurrent worker owns SourceIdentification, RustRuntimeJoin and
PrivacyR1FinalRelease; those modules are not edited. No production source,
wallet, key, security target or frozen artifact is changed.

## Stage 1 — ordered section and per-element composition

`R1Z.ProverCommitTraversal17` proves arbitrary-length append induction,
ordered 10+12 projection before sorting, the fixed order header/transcript/
openings/nodes, four-callback equality composition, and the 57,607-byte length
from the explicit successful section lengths. The transcript phase includes
compact semantic, compact y1, inactive, round0, folded root, round1 and final.
No section callback is silently identified with Rust.

J8641 failed because `prefix` is reserved Lean syntax; it is excluded.
Changed-source J8642 passes: exit 0, wall 0.76s, peak RSS 1,409,788 KiB,
swaps 0; source revision `47ccfa22c` plus exact source snapshot hash. All
seven axiom audits are empty or `[propext]`. Each attempt uses the existing
slot launcher with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
No shared existing source/object was overwritten (only this new module's
failed source was replaced); no dependency replay was needed. Exact source,
dependency fingerprints and full audit lines are in the part-17 `lean/`.

Five replacement Kani checks pass (unwinding assertions enabled):

| Target in `compact::serialization17` | Wall s | Peak RSS KiB | Exit | Swaps |
|---|---:|---:|---:|---:|
| section_header | 2.593 | 365016 | 0 | 0 |
| section_transcript_cell | 3.726 | 379988 | 0 | 0 |
| section_opening_cell | 2.933 | 375168 | 0 | 0 |
| section_node_padding_cell | 3.061 | 377268 | 0 | 0 |
| ordered_element | 2.667 | 374404 | 0 | 0 |

These spend time in Kani compilation/bounded verification, with no dense
arithmetic; Kani's MIR profile is not a native debug arithmetic release gate.
Each uses 6G/8G/no-swap/64-task scopes, four compiler jobs and the prescribed
linker flag. Source revision `47ccfa22c`, exact instrumented source hashes,
commands and full output are in `rust-attempts.json`, `*-inputs.json` and
`receipts/`. Axioms: N/A (Kani, not Lean). The unchanged production source is
copied with only cfg(kani) harnesses appended in the isolated host workspace.

The header is complete. The transcript check is one compact 32-byte cell
(including both successful emission and unchanged-prefix rejection); the
opening check is one arbitrary lane's 4/16-byte slice; the node check is one
32-byte node plus one zero padding node. Their Vec prefix is three bytes.
The ordered check covers any batch, tree and legal ordinal of the real
22-element query array, compares the source map invocation to direct
indexing, and verifies one push onto a one-element prefix. It avoids all
prior timed-out Vec/sort formulations. The Lean append induction quantifies
all lengths at its List carrier, while the Rust Vec/List bridge still needs
certification. No large-prefix Rust claim follows from a small-prefix check.
`check-source.py --check` binds the exact source expressions and refuses a
changed source snapshot; it is a text-binding preflight, not an equivalence
proof. Sorting/dedup correctness, full semantic framing, opening lane order,
node multiproof traversal, and full Rust section callbacks remain open.
The prior four primitive codec results are reused without replay or a
claimed formal import into Lean.

## Remaining concrete execution boundary

`PrivacyR1HeadlineDeployed` still quantifies an independent `FSExperiments`.
Local codec equalities cannot construct its coupling, identify its randomness
law, or establish its success/abort oracle history. No premise removal is
claimed until those concrete obligations have been proved.

## Stage 2 — borrowed cells and all-length owned-state induction

`ProverCommitLoop17.run_related` proves an induction over an arbitrary input
list. A local transition relation gives equality of status and a relation of
all retained state; the induction preserves first error and iteration order.
The relation may include vectors, hash cursors and full oracle history. Its
local-step hypothesis is explicit, not silently instantiated for Rust.
J8646 failed on missing simplification in the error branch; changed J8648
passes with `[propext]`, exit 0, wall 0.64s, peak RSS 1,409,736 KiB, swaps 0,
revision `9cb63237e` plus exact source hash in the receipt.

The Kani one-iteration gates compare the literal borrowed cell body with the
owned collector (`remaining=1`) or a fresh-state padding-cell reference. An
unconstrained scalar result and successor state are explicit relational
inputs shared by both sides. Each callback asserts its exact input state;
every final seed/counter/block/word and scalar call count is checked. Both
success and scalar exhaustion are covered. These are **control-flow checks**,
not proofs of the scalar sampler or a probabilistic oracle law. They must be
composed with the existing scalar facts, not interpreted as verified stubs.
Resetting the call-record cursor between comparisons does not reset an oracle:
these checks make no oracle call and take one fixed scalar transition as input.

| `state_only_hiding::iteration17` target | Receipt | Wall s | Peak RSS KiB | Exit | Swaps |
|---|---|---:|---:|---:|---:|
| m31_push | m31-push-v1 | 13.546 | 746508 | 0 | 0 |
| qm31_push, fixed old zero | qm31-push-v1 | 11.498 | 748732 | 0 | 0 |
| padding_row, fixed old one | padding-row-v1 | 9.829 | 721048 | 0 | 0 |
| qm31_push, arbitrary old value | qm31-push-v2 | 10.377 | 748600 | 0 | 0 |
| padding_row, arbitrary old value | padding-row-v2 | 8.495 | 720852 | 0 | 0 |

The changed v2 gates strengthen their old contents; m31 is not rerun.
The push buffers have one old entry, so the bounded Rust result alone does
not establish arbitrary-capacity vector semantics. Padding quantifies its
row/dependent/predicate and verifies zero calls on skipped rows, one call on
taken rows, no write on scalar failure, and exact retained state. It compares
one cell rather than the full borrowed 1024-row loop. `run_related` proves
all-length transport **if** the concrete source transitions instantiate its
local relation. The existing Aeneas Vec push specification and part-16 prefix
induction remain reusable but do not manufacture that source instantiation.

All Kani runs use 6G/8G/no-swap/64-task scopes, four compiler jobs and the
prescribed linker flag; time is in compilation and bounded verification.
`#print axioms`: N/A. Exact revision/instrumented source hashes and commands
are in `rust-attempts.json`, the input manifests and receipts. The v1/v2
harnesses are retained separately. No unchanged timed-out gate was rerun.

## Stage 3 — owned outer assembly extraction

`assemble_owned17` is a new proof-only Rust reference taking preallocated
owned buffers and a retained state. Its order is c1, ten mask-only columns,
g collection, g balancing, padding collection, padding balancing, final
returned material and nonce. Each call binds fresh owned values and state;
all errors return the exact state reached and suppress partial material.
It starts **after** nonce reservation, seed derivation and allocation. It
neither replaces nor proves equality of the shipped outer borrowed builder.

Charon `assembly-charon-v1` passes in optimized release mode: exit 0,
24.309s, peak RSS 673664 KiB, swaps 0. Aeneas `assembly-aeneas-v1` passes:
exit 0, 0.800s, peak RSS 102080 KiB, swaps 0. Both use the fixed host caps.
No failed borrowed-loop extraction is rerun. The LLBC is recorded by hash
and size only; raw generated Lean text, tool hashes, input source hashes and
receipts are retained in the part-17 evidence directory.

`AspisR1ProverAssembly17.{Types,Funs}` are the promoted extraction. The
promotion script makes only explicit port compatibility edits: narrow the
root import to Std/RustAttributes/Data.Discriminant, and replace the
unsupported generated discriminant attribute with the same five-constructor
explicit discriminant instance used by Material14. Generated resource
options remain exactly generated. No new handwritten resource option exists.
J8645 fails on the unsupported attribute; J8647 exposes the missing narrow
Discriminant import. Changed J8649 (Types) and J8650 (Funs) pass: respectively
1.29s/2528576 KiB and 1.63s/2546052 KiB; exit 0, swaps 0. No old shared module
was changed. The failed versions are excluded and retained in the receipts.

`ProverCommitAssembly17.extracted_stages` connects the extracted outer Rust
function to the six named monadic stages. `first_stage_error` preserves the
advanced state on rejection. Recursive collectors and balancers stay named;
no large recurrence is normalized. J8651–8653 expose only differing match
normal forms (Unit pattern and constructor branch order), not a counterexample.
Changed J8654 aligns those small matches and passes both audits using only
`[propext, Classical.choice, Quot.sound]`: exit 0, wall 1.25s, peak RSS
2525796 KiB, swaps 0, revision `45a502067` plus the exact source snapshot hash.

This closes the extraction-friendly **owned outer reference** composition.
It does not close borrowed-source all-length iteration, the extra clones /
allocation behavior, nonce/entropy/zeroization boundaries, or the nominal
type transport from the new extraction back to Material14/Returned16. No
source-to-model security premise is removed by this stage.
