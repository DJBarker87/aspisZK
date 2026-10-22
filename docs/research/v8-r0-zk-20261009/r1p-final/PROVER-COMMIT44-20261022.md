# Prover commitment continuation 44

Target not yet established. Base: a99fab97ee2cf19835eba9e1b8625de13919be43.
Branch: codex/cx-prover-commit44-20261022.

## Stage 1: D156 parent collection

Exactly one named TrustedStd field is added:
`btree_set_from_iter_ordered`, specifying the `BTreeSet<usize>::from_iter`
collection/consuming iterator as `input.toFinset.sort (· ≤ ·)` on natural
images of usize keys. `MapAPI.set_from_iter` names the native operation.
No other trusted law is added. The universal model instance witnesses
consistency. The explicit trust inventory and before/after source are under
`../../100bit-spend-path-20261013/evidence/prover-commit44-20261022/trust/`.

`ProverCommitParents44.exact_order`, `ascending`, `duplicate_free` and
`parent_iff` establish precisely the ordered, unique parents of the decoded
current level. `traversal` and `continuation` preserve an arbitrary complete
accumulator and its subsequent observer; thus they retain coin order and
state, rather than merely parent membership. These are deterministic library
transport theorems. Native caller evidence is recorded separately, not
manufactured by a source callback hypothesis.

J9536 accepts the extended TrustedStd module (1.33 s, 2,547,684 KiB, zero
swaps). J9538 accepts all six parent theorems (1.18 s, 2,533,268 KiB, zero
swaps). Exit 0; every axiom list is [propext, Classical.choice, Quot.sound].
J9537 is a rejected type-inference draft, not accepted proof evidence.
All compiles use the pinned host Env J, -M7000, MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0 and TasksMax=64. Exact source hashes,
source revision, dependency fingerprints, targets, commands and logs are in
`evidence/prover-commit44-20261022/lean/` beside the retained source snapshots.

The shared TrustedStd source/object is overwritten and snapshotted under the
branch-specific host workspace. Dependent modules used by subsequent stages
must be rebuilt against this object before their evidence is accepted.
Publication, source experiment conversion, concrete joins and endpoint remain
pending at this stage checkpoint. No shipped source changes or ELF rebuild.
