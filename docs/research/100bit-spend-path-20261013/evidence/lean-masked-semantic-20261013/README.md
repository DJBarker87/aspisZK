# Masked semantic candidate checkpoint

This evidence package records 22 focused Lean attempts across 15 final targets.
The latest attempt for every listed target exited successfully. The evidence
is a candidate-level formal checkpoint only; it does not establish source
refinement, Fiat–Shamir security, privacy, or release/security closure.

Runs used source base revision `3c17bdf902eac67d12796ef029007305b358821e`
and the pinned NUC workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`, with
Lean threshold 5000 MB, `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, and `TasksMax=128`. Receipts include exact source hashes,
exit status, wall time, peak RSS, and swap. Green targets' axiom audit allows
`[propext, Classical.choice, Quot.sound]` (some declarations use a subset); no
green target log contains `sorryAx`. Failed intermediate attempt logs retain
both placeholder `sorryAx` and self-named axioms where Lean emitted them.

| Target | Final attempt | Final status |
|---|---:|---|
| `R0P/MaskValue` | a | pass |
| `R0P/CircleSampler` | b | pass |
| `R0P/SemD2` | b | pass |
| `R0P/SemD3Glue` | d | pass |
| `R0P/SemView` | a | pass |
| `R0P/SemDecision` | a | pass |
| `R0P/SemPad` | a | pass |
| `R0P/MaskProtocol` | a | pass |
| `R0P/SemD2Glue` | a | pass |
| `R0P/MaskD2` | a | pass |
| `R0P/MaskSemantics` | a | pass |
| `R1SamplerBytePass` | c | pass |
| `R1SemanticTransport` | a | pass |
| `R1MaskedSemantic` | a | pass |
| `R1SemanticReuseCheckpoint` | a | pass |

The failed attempts are retained, not counted as green results: BytePass a/b
had source/elaboration errors; CircleSampler-a and SemD2-a exposed stale
qualified-name/prime references; SemD3Glue a/b stopped at missing cached
objects, while c exposed the stale prime reference and emitted failed-object
axioms including self-named axioms and `sorryAx`. The exact diagnostics and
per-attempt `#print axioms` output are in `attempts/` and are summarized in
[`manifest.json`](manifest.json). `R1SemanticReuseCheckpoint.lean` is an audit
module preserved as a source snapshot; its current repository source is
`docs/research/100bit-spend-path-20261013/lean/SemanticReuseCheckpoint.lean`.

[`compiled-target-objects.tar.gz`](compiled-target-objects.tar.gz) contains
only the 15 newly produced target `.olean` outputs (SHA-256
`9da8e90d043ab377c6d7a994de64d0eefef708eb703e7dd8c016496c3f2aa56d`). It
excludes external dependency-cache objects. To restore the targets in a fresh
checkout, extract the archive at this directory; its `objects/` member paths
recreate the layout. Loose objects remain on disk for the active checkout.
`manifest.json` indexes every target and attempt with receipt, source snapshot,
current source path, source hash, axiom sets, and produced object hash.
[`namespace-refactor-comparison.json`](namespace-refactor-comparison.json)
records a syntactic comparison of the qualified-name-only edits to
`CircleSampler`, `SemD2`, and `SemD2Glue`; it does not establish semantic
equivalence beyond the separate focused Lean results. `capture.json` records
the checkpoint scope and source pins.
