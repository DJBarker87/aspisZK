# Literal append gates from R1 extraction

Later checkpoint: [APPEND-TREE-BRIDGE.md](APPEND-TREE-BRIDGE.md) proves the
frozen-table recurrence and chronological root correspondence, retaining
the authenticated source-frontier invariant as an explicit premise. The
scope below describes the earlier literal-gate checkpoint.

The checked R1 candidate now carries the ordered output pair, all twenty
append-node equations, the next-root equality, and the carried frontier
entry. An explicit model of the host's checks on the other frontier entries
then determines the complete next frontier. These conclusions are derived
from the production constraint families and exact copy-link records.

This checkpoint does not yet identify the frozen empty-root table with
iterated hashing or the literal path with the chronological Merkle-tree
transition. Rust correspondence, the shared-oracle argument, and privacy
remain separate obligations. It is not a complete private-spend theorem.

## Existing proofs reused

`AppendNode.node_step` applies the existing schedule and Poseidon output
theorems, keeping the permutation opaque. Its symbolic tweak cancellation
recovers the two inputs of `nodeCompress`. `empty_target_untweak` proves
that the reduced target used in the digest gates recovers the corresponding
frozen-table entry in characteristic `2^31-1`; it does not assume or prove
the table's hash recurrence.

`AppendPair.leaf_valid` instantiates the old `PairLeaf.Valid` predicate
directly from occupancy row 1018. Four named copy records connect the pair
to the output notes. The old `valid_empty_second_commitment_zero` theorem
supplies the withdrawal's zero second slot. The resulting pair hashes are:

| Variant | Pair node proved from the gates | Additional variant guard |
|---|---|---|
| Private transfer | `nodeCompress recipient pub.change` | `pub.recipient = some recipient` |
| Withdrawal | `nodeCompress pub.change zero` | None beyond the withdrawal variant |

This does not assert knowledge of an output recipient's secret key.

`AppendCopyLinks.append_cells` projects the forty append records from the
same ordered registry already used by the source model: indices `6+2*l`
and `7+2*l` after positivity, with full tags `1124073496+2*l` and
`1124073497+2*l`. The two records select the previous node as the left or
right input according to the append-index bit. Digest gates provide the
other input, either the frozen empty root or the snapshot frontier entry.

`AppendPath.prefix_output` follows blocks 33 through 53 by symbolic
induction. At each level it hashes the previous node and the selected
sibling in the required order. `next_root` and `next_frontier_carry` use
the final public digest bindings. Neither theorem assumes its claimed
root or carry-node equality.

## Explicit public-check boundary

`AppendSemantics.NonCarryShape` models only the non-carry frontier portion
of the host's transition validation. For each level other than the carry,
it requires the next frontier entry to equal the frozen empty root when
the level is below the carry or its source-index bit is zero; otherwise
it requires the snapshot frontier entry. The premise contains no root
equality and no carry-node equality.

`afterstate_of_production` combines that premise with the proved carry
binding to determine every next frontier cell. The model's `Public` does
not itself carry the complete source leaf sequence, old-root invariant,
after-index check, or account bindings. Those source obligations have
not been silently added as conclusions.

`AppendExtraction.large_matching_extracts` strengthens the same literal
R1 candidate from `MaskedSemantic.large_matching_extracts`, retaining its
opening, typed-word, sumcheck, and candidate-wide exclusion premises.
The strengthened candidate satisfies both `ProductionHolds ∧ CopyLinkBalance`
and `GateFacts`, including the already checked note and value facts.
`strengthen_afterstate_result` separately adds the named public-check
premise for the complete frontier.

## Tree boundary still open

The last insertion is retained: the carry can equal 20. The new path proof
does not restrict it to `<20`; only the statement about an actual frontier
slot takes that bound. In the full-capacity case, the complete-frontier
theorem gets all twenty entries from `NonCarryShape`.

The old `ExactPairAppendTransition` requires a `.more` carry result, whereas
the production code also accepts the last `.full` insertion. Reusing the
generic tree correctness result therefore needs both `append_correct`
and `append_terminal_correct`, plus the source frontier invariant.
Restricting the source index to avoid the latter would change the task.

The frozen table's row zero is the hash of a zero pair, not a zero digest.
The next bridge needs its initial equation and twenty self-parent equations,
then a correspondence between `pathPrefix`/`expectedFrontier` and the
generic binary-carry tree model. The source-only inventory and exact pins
are in [APPEND-TABLE-BOUNDARY.md](APPEND-TABLE-BOUNDARY.md).

## Focused NUC evidence

Source base: `2fefd09653112d36ac284854b0ffa677bcbe9ef0`, plus the nine
source hashes recorded in the [evidence manifest](evidence/lean-append-gates-20261013/MANIFEST.json).
Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Each target ran under `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, `-j1`, and `-M5000`, reusing the pinned dependency cache.

| Target | Final attempt | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| `R1AppendNode` | c | 0 | 1.62 | 3,339,604 | 0 |
| `R1AppendCopyLinks` | g | 0 | 2.49 | 3,366,832 | 0 |
| `R1PairCopyLinks` | a | 0 | 2.70 | 3,222,524 | 0 |
| `AspisFormal/Pool/V7PairLeafOccupancy` | append-b | 0 | 1.65 | 3,187,032 | 0 |
| `R1AppendPair` | b | 0 | 1.49 | 3,241,828 | 0 |
| `R1AppendPath` | b | 0 | 1.57 | 3,341,256 | 0 |
| `R1AppendSemantics` | a | 0 | 1.49 | 3,336,516 | 0 |
| `R1AppendExtraction` | a | 0 | 1.67 | 3,586,040 | 0 |
| `R1AppendCheckpoint` | a | 0 | 1.37 | 3,570,308 | 0 |

The combined checkpoint prints twelve axiom audits, all subsets of
`{propext, Classical.choice, Quot.sound}`. The bundle retains all twenty
attempts, including eleven failures and their exact source snapshots.

The initial legacy occupancy import exhausted Lean's memory threshold
with exit 134 and 6,137,812 KiB peak RSS. Narrowing its first import from
`Mathlib` to `Mathlib.Tactic` reduced the final peak to 3,187,032 KiB.
Every theorem statement and proof body in that historical file is unchanged;
no memory cap was raised. Other failed attempts were local elaboration or
missing-dependency errors. This is a focused dependency-chain checkpoint,
not a replay of the complete historical release manifest.
