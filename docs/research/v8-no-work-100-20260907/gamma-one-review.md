# Gamma-one specialization: exact, but both guarded layouts regress

Research continuation of `e6373fdc297308657f4ea49bbc67b57a47939d22`,
2026-09-09. The preceding goal turn made progress by committing measured sort
and chord-norm savings. This turn tests the proposed gamma-head specialization,
proves its local interfaces, and rejects two slower implementations. It does
not redefine an arithmetic saving as a CU saving.

## Decision

| Complete build | Same-proof CU change | Worst observed CU | ELF bytes |
|---|---:|---:|---:|
| **Retained chord-norm** | baseline | **1,095,156** | 1,007,728 |
| Guard inside each dot | +1,022 | 1,096,178 | 1,006,728 |
| Dispatch once per query | +647 | 1,095,803 | 1,016,808 |

Each regression is exact across all12 identical maximum-body accepted proofs,
covering transfer/withdrawal and current/rollover pages. Each control passes
its24-case maximum-body matrix with matching expected acceptance/rejection,
proof hashes, protected accounts and settlement. Pool, Registry, Token3.5 SBF,
driver and runtime are unchanged. Unsupported rollover stale/replay cases
are not counted. Neither loser was expanded into ordinary/rollback matrices.

**Both are rejected for performance.** The selected query and callback sources
were restored byte-for-byte to the starting revision, both locally and in the
task-owned NUC copy. No existing user change was reverted. The retained ELF
was not overwritten or rebuilt unchanged. The runners now refuse these
control names unless their exact archived source patches have been installed;
a refusal was exercised after restoration (expected exit2 before a build).

The best measured complete shapes remain1,063,909 /1,076,729 /1,082,205 /
1,095,156 CU, with104,844 CU worst-observed headroom under the real1.2M TxV1
cap. Bodies remain **40,282 bytes**. Same-pool V7 remains23,086 /42,328 /
45,840 /46,272 CU cheaper. These are fixture maxima, not universal CU coverage.
See [exact results](gamma-one-results.json) and the retained
[chord-norm evidence](chord-norm-review.md).

## What was tested

The actual generated gamma power table starts at QM31 one. Its first C1
coefficient has limbs `[1,0,0,0]`, so its contribution is the first decoded
M31 value in channel0 and zero in the other three channels. But the generic
prepared-table API also permits arbitrary tables, and existing tests rely on
that interface. An optimisation cannot silently assume all such tables are
actual power sequences.

The experimental `GammaKernel` constructor compares the complete head once
and holds an immutable borrow plus a private derived flag. The callback
constructs it once outside its22-query loop. For each dot, the fast branch
replaces only the first four-product chunk; the other chunks, partial reduction
boundaries, final balanced sum and C2 helper products remain unchanged. When
the head is not `[1,0,0,0]`, it uses the original generic computation.

The first control leaves the derived-flag branch inside the dot. The second
control chooses `gamma_prepared::<true/false>` before each query's decoder,
so the inner specialization is a compile-time constant. This is an explicitly
different implementation hypothesis, not an unchanged retry. It improves375
CU over the first control but remains647 CU worse than the retained verifier.

The arithmetic model omits352 base products (9,152→8,800 for C1 across the
whole proof), while preserving2,464 partial reductions. The equality test,
stored flag/borrow, dispatch, accesses and code layout cost work too. One head
comparison is **not** a claim of one machine branch: the first control still
has source-level inner decisions, while the split version has22 outer
dispatches before compiler optimization. Exact emitted branch counts and an
instruction-by-instruction attribution of the regression were not measured.
There is no new heap allocation; the kernel metadata is stack-borrowed.

Neither version changes a canonicality check, image/row/query relation,
authentication path, field, challenge, proof byte, or nonce. No prover run or
search was performed; the archived proofs are reused without cherry-picking.

## What Lean establishes

[GammaOne.lean](experiments/GammaOne.lean) models the guarded first chunk as a
**total** function of an arbitrary four-limb head, channel, decoded value and
remaining three-product sum. It proves:

- Guarded output equals the original integer expression, whether or not the
  head is one; an arbitrary reducer/continuation therefore sees the same input.
- Canonical operands and the three-product tail give the original four-product
  u64 bound. Every nonnegative intermediate prefix below that sum has exact
  wrapping behavior. No fifth product or signed accumulator is introduced.
- Moving a public dispatch before common `Except` decoding preserves success
  **and errors**, without assuming the decoder succeeds.
- Removing the guard for an arbitrary table is false: head2/value1 gives2,
  whereas unconditional one-specialization gives1.

The existing GammaDotUnroll/M31 range results continue to justify unchanged
remaining chunks; they were not replayed unchanged. The new source boundary
is explicit: the private Rust flag comes from the actual head comparison and
cannot be changed while its immutable powers borrow is live. The finite-array
comparison, safe Rust borrow semantics, source decoding/body correspondence,
and compiler/SBF remain audited/tested, not a complete translated-source proof.
The decoder-error lemma is an algebraic control-flow model, not an assertion
that a Bool field alone proves source correspondence.

Each optimized Rust control passes2,048 arbitrary canonical table/vector
profiles, with roughly half using the identity head and the others exercising
the fallback, plus16 head near-misses. An independent u128 dot checks all four
channels. The existing512 packed gamma profiles, maximal-limb non-power
matrix, all152 noncanonical packed positions and short-input failures also
pass. A deliberate forced-true call demonstrates the unguarded counterexample.
These synthetic tests do not measure a soundness probability.

## Resources and provenance

| Focused job | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Guarded optimized test/build | 0 | 21.04 | 514,580 | 0 |
| Guarded SBF build | 0 | 33.91 | 591,128 | 0 |
| Split optimized test/build | 0 | 21.16 | 515,784 | 0 |
| Split SBF build | 0 | 33.79 | 592,272 | 0 |

Compilation dominates. Build scopes High5/Max7 GiB/jobs2; SVM High3/Max4 GiB;
all SwapMax0. NUC Rust1.94.1, cargo-build-sbf2.3.0/tools1.54, checked optimized
SBF Rust1.89-dev and LiteSVM0.16.0/runtime4.2.1 are unchanged. Both executed
ELFs have direct-r10 offsets≤4,096 and no new stack warning. This is not a
whole-machine stack proof. The selected Solana testing workflow keeps the
decision at matching complete transactions, not the multiplication model.

Final Lean4.32.0/Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` replay:
exit0,3.44s,2,878,554,112-byte RSS,zero swaps. Seven axiom audits contain only
standard `propext`, `Classical.choice`, `Quot.sound`; the dispatch lemma uses
none. No retained `sorry` or new axiom. The first leaf preflight failed because
`prefix` is a reserved token (11.88s,2,819,276,800-byte RSS,zero swaps). Renaming
it yielded the six-lemma intermediate success (5.70s), then adding the actual
dispatch-error lemma justified the final changed-file replay. These logs are
separate; the failed preflight is not claimed proof evidence.

`audit_gamma_one.py` replays each literal source patch **in memory** against
the full starting revision and checks recorded hashes, proofs, programs,
resource logs and final axioms. Current selected-source hashes after local/NUC
restoration are:

```text
query_arithmetic.rs 57590907abf1c6a278cca0babc49b4c916a87a0a44e1f265b9bea28cc9fd52b1
relation_callback.rs 50854e443ad4c913ff5216a217502ea956d1820ca2e5840bd0e2f69cf71a3b2a
```

The rejected source is preserved in `gamma-one-query.patch` /
`gamma-one-split-query.patch`, with the shared `gamma-one-callback.patch`, not
left in the selected Rust path. Apply the chosen pair to an isolated task copy
of the starting revision (`git apply --recount`), then run:

```sh
bash experiments/run_gamma_one_nuc.sh NEW_TEST_LOG
bash experiments/run_complete_build_nuc.sh gamma-one NEW_BUILD_LOG
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh gamma-one NEW_MAX_DIRECTORY
```

For the split control use its query patch, `run_gamma_one_split_nuc.sh` and
mode`gamma-one-split`. `experiments/` abbreviates this research directory.
The runners require exact source hashes before spending build resources.
Locally, `run_gamma_one_lean.sh NEW_ABSOLUTE_LOG` replays only the changed leaf;
`audit_gamma_one.py` validates retained evidence without heavy reruns.

No production/main/default changes or deployment occurred. Global recovery,
adaptive full-view ZK and resource-bounded FS keep their prior status, with zero
work credit. The accepted body census is unchanged:
`697*16+52+24+22*621+2*296*26 = 40,282`.

## Next bounded experiment

Do not retry either guard layout unchanged or silently remove the guard from
the generic API. The stronger next target is the **five-coefficient circle
specialization of the already-winning chord norm**. First connect the actual
log20 point constructor to `x²+y²=1`: verify the pinned window tables and prove
closure of the source's point addition symbolically, rather than reducing all
262,144 points in Lean. Then instantiate the existing `circle_even` lemma to
remove the redundant y² norm term. Keep zero-denominator/norm rejection and
the general reference for differential tests. Only measure after that input
invariant is justified; reject the control if preparation/layout costs erase
the complete-transaction saving. This moves to a different, measured-winning
component rather than repeatedly polishing the rejected gamma-head path.
