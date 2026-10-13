# Concrete empty roots and chronological append root

The frozen empty-root recurrence and the chronological append-root bridge
now compile. This extends the [literal append checkpoint](APPEND-GATE-BRIDGE.md):
the same extracted R1 candidate determines the root of the old leaf sequence
followed by its ordered output pair, given the authenticated old-frontier
invariant. The last insertion, which fills the tree, is included.

This is a field-model theorem. It retains the old-frontier invariant as an
explicit input and does not prove that Rust execution or stored accounts
satisfy it. The subsequent [state-preservation bridge](APPEND-STATE-BRIDGE.md)
proves the stored frontier representation and abstract invariant continuation.
Source refinement, shared-oracle soundness, and privacy remain open.

## Concrete table certificates

`FrozenEmptyRoots.initial` proves, over any field of characteristic
`P = 2^31-1`, that frozen row zero is `nodeCompress zero zero`.
`FrozenEmptyRoots.successor` proves that each of the remaining twenty rows
is `nodeCompress previous previous`. Neither theorem assumes these equations.

The certificate method reuses the round-splitting pattern already present
in `AspisFormal/Poseidon2Kat.lean`. Its generic combiner is stated directly
against the current R0P permutation, avoiding an unproved identification
with the older KAT model. Each node has 24 independently pinned states:
the input, the leading linear layer, and the 4+14+4 round outputs. Lean
checks each one-round transition using kernel `decide`, then
`R0P.poseidon_chain` composes those transitions symbolically. It never
evaluates a whole multi-round recurrence in one reduction.

The data generator compares all Lean/Rust literal constant arrays, computes
the witness states, verifies their canonical ranges and frozen outputs, and
has a deterministic `--check` mode. Those Python checks are preflight
evidence; the round certificates establish the Lean equations independently
of trusting the generator. `PoseidonMap.map_nodeCompress` proves that
compression commutes with a ring homomorphism. Applying the canonical map
from `ZMod P` transports the checked equations to the wider field used by
the semantic proof.

## Existing tree theorems reused

`AppendTreeRoot.sourceFrontier` converts the public frontier to the old
generic representation, a low-to-high list of optional subtrees. A zero
index bit yields `none`; a one bit yields the corresponding public snapshot
digest. The pair-tree empty leaf is the compressed zero pair.

`frozen_recursive` identifies the now-proved table with the old
`recursiveEmptyRoot`. `reconstruct_ofFn_chain` folds an arbitrary indexed
sequence of parent transitions into the old `reconstructFrom` function.
Together these prove `path_reconstruct`: the literal twenty-node path is
exactly generic reconstruction starting with the new pair leaf.

`append_reconstruct_afterstate` then reuses four existing theorems:

| Generic carry result | Existing reconstruction theorem | Existing chronological theorem |
|---|---|---|
| `.more updated` | `appendCarry_reconstruct_more` | `append_correct` |
| `.full root` | `appendCarry_reconstruct_full` | `append_terminal_correct` |

The only input beyond the abstract parent, empty leaf, and tree data is
`FrontierInvariant` for the old frontier and old leaf sequence. This invariant
contains authenticated subtree blocks, depth, leaf count, and available
capacity. The new root equality is a conclusion in both cases.

`AppendTreeRoot.next_root_correct` combines this result with the production
gates. Its conclusion is:

```text
pub.nextRoot = rootWithEmptySuffix nodeCompress emptyPair 20
  (oldLeaves ++ [outputPairNode])
```

`AppendTreeExtraction.strengthen_candidate_result` attaches that equation
to the same member of the literal R1 candidate list, preserving its production
constraints, copy balance, and previously derived gate facts. For transfers
the pair node is the ordered recipient/change hash; for withdrawals it is
the change/zero hash, under the earlier variant guards.

## Verification and remaining boundary

Source base: `3a73ee4bb67558ffbc608abfea81d74b4d2fa2a4`, plus the exact
source hashes in the two evidence bundles. All 53 final focused targets
passed on the pinned NUC with Lean 4.32.0, `-j1`, `-M5000`, and per-job
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`.

The final `R1AppendTreeCheckpoint-a` passed in **1.39 seconds**, peak RSS
**3,590,024 KiB**, zero swap. Its ten axiom audits are subsets of
`{propext, Classical.choice, Quot.sound}`. The exact targets, statuses,
timings, hashes, source snapshots, runner, and compiled objects are in:

- [Concrete certificate evidence](evidence/lean-empty-roots-20261013/manifest.json):
  43 final targets and one preserved dependency-ordering failure.
- [Generic and tree bridge evidence](evidence/lean-append-tree-20261013/source-manifest.json):
  ten final targets and fifteen failed attempts. One superseded failure,
  `R1PoseidonMap-a`, retains its hash/logs/receipt but its exact source
  snapshot was not preserved; every final successful source is retained.

The first table aggregation hit a heartbeat limit while simplifying the
zero-input hash. The replacement keeps the hash opaque and uses an explicit
map-of-zero equality; the final aggregation takes 1.45 seconds with the
same limits. Other failures were local proof plumbing, a missing narrow
import, or the recorded checker-before-data ordering error. No cap was raised.
`FormatV1` and `IncrementalMerkleV1` have narrower imports; all their theorem
statements and proof bodies are unchanged.

This focused dependency chain was checked once through its final combined
target. It is not a replay of the complete historical release manifest.
The subsequent [state-preservation bridge](APPEND-STATE-BRIDGE.md) identifies
the stored next frontier with the generic carry result, including the
full-capacity state, and proves abstract initialization/continuation under
an explicit state link. Account-level source/codec/settlement, Fiat–Shamir,
and zero-knowledge obligations remain explicit; these deterministic theorems
do not alone establish a 100-bit private spend.
