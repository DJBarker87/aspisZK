# Prover commitment continuation 45

Target not yet established. Base 6143f773e8fc8bcc345b70f6d63484e701dc5b2a;
branch codex/cx-prover-commit45-20261022.

## Stage 1: D157 library interfaces

Three named TrustedStd fields are added: `btree_len` (length of the decoded
ordered entries, native usize natural image), `slice_sort_ascending` (ascending
stable merge sort of scalar natural images), `vec_dedup_adjacent` (adjacent
unequal destuttering, retaining the first equal element). Call sites:
`crates/aspis-r1-cost-probe/src/sim.rs:389` and `:491` (level/transcript length),
`:473` (sort/dedup of the batch's u32 indices). Allocation totality is not
asserted. No other trust item is added. The model instance still witnesses
consistency; it does not verify Rust collection internals.

`ProverCommitStd45` proves exact sort/dedup equality, ascending order,
no duplicates, membership and arbitrary stateful-consumer transport. The
map-length theorem identifies native length with ordered iteration. Both
root-guard outcomes and the resulting success/Merkle error are transported;
this is guard refinement, not a theorem that arbitrary trees succeed.

J9624 accepts the initial Boolean-relation spelling; J9625 accepts the final
Prop-relation spelling of the same adjacent-inequality semantics. J9626
accepts all eight new transport theorems. Exit 0, zero swaps, standard axioms
[propext, Classical.choice, Quot.sound]. Exact targets, source revisions and
hashes, dependency fingerprints, commands, wall time, peak RSS, errors and
full axiom output are in
`../../100bit-spend-path-20261013/evidence/prover-commit45-20261022/lean/`.
The shared TrustedStd source/object was overwritten and its predecessor
snapshotted under the branch-specific host workspace. Consumers must be
rebuilt against the new object before their evidence is used.

Publication, experiment conversion and endpoint remain pending at this
checkpoint. No shipped source changed and no ELF rebuild is triggered.
