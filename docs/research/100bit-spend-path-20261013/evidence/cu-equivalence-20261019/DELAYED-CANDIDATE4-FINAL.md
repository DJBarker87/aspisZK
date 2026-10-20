# Candidate 4: delayed base-dot reduction

**Complete exact helper equivalence and unchanged-context substitution checked.**
Candidate `d11f9b2fcbddf68fd1ffec297f987de0aa95a6c0` versus exact parent
`534437acc6ff60dd20a84ca1393fe8f4e09341ff`.

The measured saving being justified is **62,101–62,184 combined CU**:
stage 1 **28,221–28,252**, Pool settlement **33,880–33,932**, across the six
retained fixtures. This proof adds no further CU saving. Production Rust and
the frozen runtime artifact are unchanged. Existing codec, 583-call ordered
trace, checkpoint23, injection, strict stack and CU replay evidence remains
in `../cu-savings-20261019/FINAL-REPORT.md`; those suites were not repeated
for Lean-only changes.

`CuSavingsDelayedCandidate4.kernel_equivalence` proves equality of the entire
source-emitted old/new `four_dots` functions, on **every query slice and gamma
carrier**, under the shared reference runtime interpretation. It preserves
successful outputs, failure values and divergence. There is no canonical-input,
child-success, bounded-product or candidate-equivalence premise.

The reason caller canonicality does not need another proof is that the whole
multiply/add/decode traversal is identical on both sides. Any overflow or
rejection in that traversal is shared. Every successful batch is a `u64`;
its partial fold fits below `2^34`. The source iterator executes exactly seven
batches; the running bound remains below `2^37`. The old canonical accumulator
and new partial accumulator have identical residues at every updated limb.
Actual final reductions produce the same eight words. The unchanged tail and
four-slot constructors then preserve the complete result. Bounds are symbolic;
no large recurrence is normalized.

`query_context` proves substitution through the complete common prefix and
suffix of the single call. `all_callers_equivalence` proves arbitrary
computational context substitution by function extensionality, covering repeated
calls too. The source audit checks that **the sole Rust delta is `fast_dots.rs`**,
that the only production invocation is `query_with_geometry`, and that its
`query`, `tx1_finish`, `tx1`, `tx2` and `tx2_authenticated` source contexts are
unchanged. Exact context fragments and hashes are retained. These contexts are
**not separately re-extracted transaction bodies**: their transfer uses
unconditional helper equality and the existing compositional source/runtime
boundary. No proposition assuming context or transaction equivalence is added.

The frozen producing revision `39c2971dd16c95858a4cfd2c9ae35da052eacfa9` adds
only candidate 10's fixed-prefix conversion to this helper. The audit checks
that removing those exact added bytes yields the candidate-4 helper. The
unchanged pairing/from-limbs/tail operations are universally quantified
computations, with no algebraic or success laws; subsequent common changes to
those operations do not invalidate this local replacement result. Candidate 10
and the other outstanding replacements are not thereby declared closed.

Twelve selected Lean targets pass, with exact source/object/cache pins and
command, features, revision, exit, wall time, peak RSS, process swap and cgroup
swap in `DELAYED-CANDIDATE4-FINAL.json` and the per-attempt receipts. The final
bridge took **1.604 s**, peaked at **2,378,280 KiB RSS**, and recorded **zero
process/cgroup swap**. Its `#print axioms` audit has only `propext`,
`Classical.choice`, `Quot.sound`, and inherited `core.fmt.Formatter : Type`;
there is no `sorryAx` or added equivalence axiom. The source-extracted
`array::from_fn` admission is reused and checked by the final bridge.

The initial original-producer closure match failure is retained. The existing
source-preserving no-branch-join producer emitted the complete exact functions;
no producer repair or disabled validity check was introduced for this task.
One otherwise successful kernel check observed another host Lean process at
launch. That receipt remains historical; the accepted kernel was replayed on
an idle host with no foreign Lean job and produced the identical object hash.
Every selected final receipt reports no foreign Lean job at launch.

The remaining trusted boundary is the existing Rust/Charon/Aeneas translation,
primitive/iterator semantics and sufficient stack/resources. This is not a
compiler, machine-code, universal CU bound, or whole-bundle soundness/privacy
proof. The changed helper performs no hash/observer operation; the transcript,
proof bytes and public encoding are untouched. The retained six-case runtime
maximums remain 1,199,687 CU stage 1 and 1,188,496 CU settlement.

Candidate 4 joins candidates 6 and 12: **3 of 10 retained replacements closed**
within their stated source/runtime boundaries. The next largest remaining
measured saving is candidate 3, fixed S2 inactive groups: **40,517–40,520 CU**
in settlement. No new goal is created here.

Re-pin inventory: `DELAYED-CANDIDATE4-DECLARATION-REPIN.json`.
Reproduce source/receipt audit:

```sh
python3 docs/research/100bit-spend-path-20261013/tools/cu-equivalence-20261019/check-delayed-candidate4.py
```
