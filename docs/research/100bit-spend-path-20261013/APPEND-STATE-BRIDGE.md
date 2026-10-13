# Reusing the chronological tree invariant across spends

The R1 field model now proves that the saved frontier is the generic tree's
actual append result. It also proves initialization at index zero and reuse
of the invariant by a subsequent spend that reads the saved state. This
extends the [root-only checkpoint](APPEND-TREE-BRIDGE.md); it does not certify
the Rust account implementation, Fiat–Shamir soundness, or privacy.

## Exact statement and premises

`AppendTreeState.of_production` takes the existing production constraints and
copy balance, `NonCarryShape` (the literal non-carry public guard), and the
authenticated old-frontier invariant. It concludes all previous note/pair
gate facts plus `StateFacts` for the same ordered output pair:

- The public new root is the chronological root after appending that pair.
- Every inactive saved frontier cell equals its canonical frozen empty root.
- If the carry is below level 20, the saved frontier satisfies the old generic
  `FrontierInvariant` for exactly the old leaves followed by the output pair.
- If the carry reaches level 20, the appended sequence has length `2^20`,
  every raw frontier cell is its frozen empty root, and its option-valued
  representation is twenty `none` cells. No open-capacity invariant is
  asserted for this terminal state.

No equality for the generic append result, new root, or post-state invariant
is an input premise. The old invariant and the public non-carry guard are
explicit inputs; source correspondence for those inputs remains open.

`AppendStateExtraction.strengthen_candidate_result` adds these facts to the
same member of the existing R1 joint candidate list. It neither chooses a
new list nor changes any extraction or probability assumptions.

## What was reused and what was proved

The existing `IncrementalMerkleV1.FrontierInvariant.append_preserves`,
`append_terminal_correct`, and `genesis_invariant` do the tree reasoning.
The new work is the deterministic representation bridge:

| File | Checked connection |
| --- | --- |
| `AppendBits.lean` | Bounded trailing ones identify the first zero bit; adding one clears lower bits, sets the carry bit, and preserves higher bits. |
| `AppendCarryIndexed.lean` | Generic `appendCarry` consumes the occupied prefix, stores its carry at the first empty slot, or returns the full root. |
| `FrontierIndex.lean` | The value of the indexed option frontier is `index % 2^depth`, hence the exact index below capacity. |
| `AppendFrontierShape.lean` | The literal saved frontier, interpreted at `index+1`, is exactly that generic result; inactive raw cells are canonical empty roots. |
| `AppendTreeState.lean` | The production gates and non-carry guard imply the chronological root and saved-state facts. |
| `AppendStateIndex.lean` | Genesis, leaf count, full-tree index, and continuation through an explicit state link. |
| `AppendStateExtraction.lean` | The same extracted candidate retains all these facts and the next live-source invariant. |

The bit and list proofs use structural induction and division/remainder
identities. They do not enumerate the `2^20` possible indices or evaluate any
hash recurrence.

`StateLink pub next` states only the two concrete read/write relationships:
`next.nextPairIndex = pub.nextPairIndex + 1` and
`next.snapshotFrontier = pub.nextFrontier`. Together with both live-index
bounds and the proved state facts, `next_invariant` supplies the authenticated
old-frontier invariant for the next spend. If the first spend fills the tree,
`full_index` proves the next index is capacity, contradicting the next live
source's strict bound. The final insertion itself remains allowed.

These assumptions match the shapes of the source checks:
`pair_forest_semantic_terminal.rs:180–208` checks the source index, its
increment, and non-carry frontier cells; `incremental_merkle.rs:181–225`
implements ordinary and full carries; `pair_tree_profile.rs:443–463` rejects
a full state as a new live source. These are inspected source correspondences,
not a proved Rust refinement.

## Verification

Base revision: `fd4aff50d1c5d977b6dda12e01356e3a1f0d258a`.
Eight focused targets passed on the pinned NUC, followed through one new
combined checkpoint. The checkpoint is one of those eight targets, not an
additional full regression. All 13 final axiom reports contain only subsets
of `propext`, `Classical.choice`, and `Quot.sound`.

The final checkpoint used 1.47 seconds, 3,591,216 KiB peak RSS, and zero swap.
The largest final target was the extraction bridge at 3,609,132 KiB. Each run
used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and the existing host
reservation check. Lean was 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

The [evidence bundle](evidence/lean-append-state-20261014/source-manifest.json)
records all successful and failed attempts, exact source snapshots, object
hashes, runner/environment, and raw resource logs. `AppendCarryIndexed` is
the one module without the `R1` filename prefix; the downstream import uses
that checked name. The initial downstream import-name failure is retained.

## Remaining security boundary

This closes initialization and preservation of the abstract frontier model
under its explicit state-read/write link. It does not establish that account
initialization, persistence, decoding, settlement, or adversarial Rust
execution implement that link and its guards. Input-note pair occupancy and
the authenticated forest path still need their full semantic connection.
The 33-round shared-oracle Fiat–Shamir instantiation and complete privacy
argument remain separate obligations. These deterministic proofs alone do
not establish a 100-bit private spend.
