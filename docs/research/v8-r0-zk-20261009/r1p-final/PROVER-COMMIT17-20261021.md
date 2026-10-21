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
