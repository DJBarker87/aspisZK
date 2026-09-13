# R10 semantic-cut evidence

Scope: the pure, fixed-context H1 influence cut only.  This evidence does not
assert transcript privacy, a simulator, C1/C2 root simulation, publication, or
any probability bound.

## Source and pack preflight

The R10 manifest check passed (39 files).  `check_source_pins.py` matched every
pinned blob against source commit `332c3569c0868f3b43e5e146f5df3cf4ee1e5627`.
The pack correctly records that the dependency closure is not proved.

`python3 verify.py` passed all 46 supplied tests.  Its full-scale demonstration
is retained as synthetic evidence only; it is not cited as a source theorem.

## Formal leaves

The cached Lean workspace compiled the five R10 leaves and aggregate
`AspisV8R10.lean` with `lake env lean -j1 -M1800`:

| target | result | axioms |
| --- | --- | --- |
| `CopySlope.lean` | pass, 1.54 s, peak RSS 1.35 GB | `propext`; selected-terminal theorem also `Quot.sound` |
| `DegreeBound.lean` | pass, 1.76 s, peak RSS 1.66 GB | `propext`, `Classical.choice`, `Quot.sound` |
| `Compaction.lean` | pass | `propext`, `Classical.choice`, `Quot.sound` |
| `AffineCertificates.lean` | pass | `propext`, `Quot.sound` |
| `KernelFibers.lean` | pass | affine fiber: `propext`, `Classical.choice`, `Quot.sound`; additive transport: `propext` |
| `AspisV8R10.lean` | pass, 3.64 s, peak RSS 1.66 GB, swap 0 | union of the above |

These are algebraic lemmas with explicit premises; none closes a source
correspondence or privacy game.

## Genuine compiler/evaluator integration

`crates/aspis-prover/tests/r10_semantic_cut.rs` is research-only and requires
the existing `insecure-spend-fixture` feature.  It constructs a deterministic,
source-valid private-transfer fixture, compiles its real sixteen 1024-row C1
columns, and uses these pinned functions:

- `compile_pool_v1_pair_forest_private_transfer_merged_c1_v1`;
- `evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1`;
- `evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1`.

It holds the genuine C1 fixture and challenges fixed, extracts all 28-by-512
H1 multipliers from the actual Copy evaluator, and checks three explicit
balanced pads supported only on frozen inactive rows.  For each pad it compares
the induced coefficient vector with the difference of the complete masked
selected terminal, checks compact coefficient reconstruction at all 28 nodes,
checks `c0`, reconstructs `c1`, and verifies zero H1 influence in `c12..c27`.
It separately interpolates every Copy multiplier from 28 points, rejects any
coefficient above degree 10, and confirms the 11-point route equals the
reference route.

Focused command:

```text
cargo test --release -p aspis-prover --features insecure-spend-fixture \
  --test r10_semantic_cut -- --nocapture
```

Result: pass (1 test), 3.92 s wall, 144,621,568 maximum RSS, zero swaps.
This is an optimized focused host test; no SBF build, proof construction,
wallet action, deployment, or production-path change occurred.

## First remaining source-specific obligation

The result conditions on an H1 pad while C1, mask-only columns, G, challenges,
and public prefix are fixed.  The first unclosed source bridge is therefore a
joint distribution/coupling statement for the real mask material, not another
rank sample: `state_only_hiding.rs` derives one seed, expands C1/mask-only/G,
then expands the inactive H1 coordinates and balances the dependent coordinate
(lines 430--469); `v6_onefold_prover.rs` builds the real Copy helper and applies
that H1 padding (lines 1281--1304).  A proof must establish the required
conditional law of this joint seeded expansion, including its transcript
binding and rejection/publication behavior.  The fixed-context test neither
assumes nor proves that law.

Existing C1 q4/q6 negative regressions, fixed-block hiding observations, and
full-transcript obligations remain separate and untouched.
