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

## Stage 2: native parent transition and eighteen levels

The per-parent native transition check passes all checks for arbitrary full
32-byte child/coin/root values and all source depths 0–17 and parent indices
below 2^17. It checks lazy left-then-right missing-child coins, the final-level
root substitution, both writes, one read-count increment, and the complete
ordered binary-parent call. The source body is retained verbatim except
`reads+=1` becomes `*reads+=1` for the harness's caller-owned counter.
Map get/insert and the recording digest callee remain explicit substitutes
at their named boundaries; no collection internals are claimed verified.
The accepted gate is `parent-transition-v3-eighteen-levels`: exit 0,
2.975 s, peak RSS 227,796 KiB, zero swaps. V1 fails a 96-byte `memcmp`
unwinding assertion. V2 passes on a 17-level stand-in but is superseded;
V3 checks the actual 18-level source domain and an arbitrary selected byte
of every returned digest. Neither earlier draft is the accepted final gate.

`ProverCommitParentStep44.step_decode`, `loop_decode` and `collected_loop`
transport both maps, lazy coins, the retained programming-call log and reads
through the native ordered parent sequence. `child_index_bound` proves the
binary child indices fit the source domain symbolically.
`ProverCommitTree44.level_decode`, `levels_decode`, `range_levels` and
`eighteen_levels` compose the state across the native depth order, preserving
every stored children map and subsequent coin state. These are caller/control
theorems; they do not identify the remaining concrete hash/codec/multiproof
callees or constitute a full publication certificate.

J9617 accepts the parent step (1.28 s, 2,541,736 KiB, zero swaps);
J9621 accepts the depth composition (1.39 s, 2,544,484 KiB, zero swaps).
Every axiom list is standard. J9619 is a rejected range-lemma draft.
J9540 was refused before compilation because an unrelated historical receipt
already occupies it; that receipt is not copied or attributed here. The
subsequent numbers were selected from a read-only receipt inventory.

The unchanged publication algebra, merge and salt consumers are rebuilt
against the extended TrustedStd object: J9539 (`ProverCommitPublication33`),
J9618 (`ProverCommitMerge33`) and J9620 (`ProverCommitLeaves43`), each exit 0,
zero swaps and standard axioms. These overwrite shared source/objects only
with the same tracked source bytes; branch-specific snapshots retain the
previous source/objects. Other dependent release modules have not been
replayed and no coherent release replay is claimed.
