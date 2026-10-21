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

Rust cell checks are in progress and will be recorded separately. The prior
four primitive codec results are reused without replay or a claimed formal
import into Lean.

## Remaining concrete execution boundary

`PrivacyR1HeadlineDeployed` still quantifies an independent `FSExperiments`.
Local codec equalities cannot construct its coupling, identify its randomness
law, or establish its success/abort oracle history. No premise removal is
claimed until those concrete obligations have been proved.
