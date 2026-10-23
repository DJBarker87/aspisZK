# Part 54: owned simulator encoder

Target not yet established. Branch `codex/cx-prover-commit54-20261023`.
Allocated attempts J10600–J10699 only. No shipped source is changed.

## Endpoint before/after

Verbatim endpoint modules are retained in `endpoint/before.lean.txt` and
`endpoint/after.lean.txt` under the part-54 evidence directory. Both currently
retain the deployed RustProverRefinement premise. No payload equality is claimed.

## Stage 1: explicit encoder owner

The owner uses an explicit finite recursive strided collector and a finite-height
evaluator. Four channel vectors are built without iterator adapters. Extraction,
source binding, native equivalence and model induction are separate obligations.

Charon/Aeneas succeed (1.458/0.476 s, 210996/71280 KiB, zero swap).
J10603 checks the exact extracted declarations after byte-identical arithmetic
rebinding. J10608 proves the complete strided collector output, including every
read index, output ordering, finite termination, and release wrapping bounds.
It exits 0, 2.53 s, 4118444 KiB, zero swap; all four printed axioms are standard.

J10600 exposes missing Lean 4.32 core companion artifacts. J10601 is refused
without a compiler invocation. The cache completion adds read-only links, and
the dependency fingerprint now records the actual split core artifacts. J10602
exposes two omitted conversion imports, repaired by reusing byte-identical
Samples49 declarations. J10604–07 are rejected collector proof drafts; their
full diagnostics are retained. No cap or heartbeat limit is raised. Receipts
pin source revision and exact source/dependency hashes. The accepted source
has no proof holes. No shared object is overwritten.

## Stage 2: owned evaluator, channel array and fibre output

J10611 proves success, canonicality and the exact recursive polynomial value
for arbitrary canonical 2^h coefficients (h≤8), with both split vectors derived
from reads. J10614 composes all four 256-coefficient channels. J10615 checks
the newly extracted phi/wrapper; retained extracted callees are byte-equal.
J10616 proves the complete owned encode_with_nodes result at supplied canonical
nodes and fibre coordinates. J10617 proves symbolically that this recurrence,
at a repeated-doubling node sequence, equals the natural Chebyshev-product
basis sum. Node equality is not inferred from that generic identity.

Accepted Lean attempts (exit 0, zero swap, standard printed axioms only):

| Attempt | Exact module suffix | Wall s | Peak RSS KiB |
|---|---|---:|---:|
| J10611 | R1Z.ProverCommitEncoderEval54 | 2.96 | 4136436 |
| J10614 | R1Z.ProverCommitEncoderChannels54 | 1.96 | 4110920 |
| J10615 | AspisR1ProducerRelease47.EncoderLeaf54 | 1.09 | 2636620 |
| J10616 | R1Z.ProverCommitEncoderLeaf54 | 1.70 | 4100276 |
| J10617 | R1Z.ProverCommitEncoderMath54 | 1.86 | 4114712 |

J10609/10 are conversion/division drafts. J10612 exposes concrete array
reduction under change; J10613 proves all theorems but rejects a duplicate
local attribute. J10614 uses an opaque array and symbolic length lemma.
No limits are raised. The second extraction exits 0/0, 1.811/0.494 s,
210944/71808 KiB, zero swap.

Kani proves arbitrary current even, odd and channel iterator read contracts
(even-v2, odd-v2, channel-v2), then split/channel iteration comparisons
using stub_verified (split-v3 and channel-iteration-v3). Each contract has its
own successful proof_for_contract harness. This checks a single transition at
the selected remaining suffix; full native iterator-state/Vec composition is
not inferred. Values are unrestricted u32 cells, with no arithmetic
performed in the collector. Source spans and the projection boundary are
in native-source-pins.json.

The broad nth(k) diagnostic even-v1 was stopped at 6460452 KiB (142.114 s),
zero swap. It is replaced by a local transition contract rather than retried.
The split-v2 CLI preflight omitted Kani's stubbing feature and is rejected; v3
changes the feature set. Accepted native wall/RSS KiB: even-v2 6.252/496312;
odd-v2 7.174/583172; channel-v2 10.571/339116; split-v3 2.996/266596;
channel-iteration-v3 9.193/189240. All exit 0, zero swap, explicit opt-level=3,
6G/8G/zero-swap/64-task scope. Raw logs and input snapshots are retained.

The native caller instantiates encode_at at M31 and QM31, whereas the
current extracted owner is WideExact. Embedding those specializations, exact
nodes_for provenance, leaf assembly and semantic/opening caller remain
explicit. This stage does not establish native simulator payload equality.
