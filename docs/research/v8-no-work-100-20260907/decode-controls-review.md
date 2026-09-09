# Decoder construction wins; four-channel gamma fusion regresses

Research continuation of `7ccf84a3b8c66c30a9db96fb9cb305849b65106b`,
2026-09-09. The preceding turn was **progress**: it committed and measured
Merkle/leaf savings. This turn profiles the remaining arithmetic, rejects one
slower control and retains a smaller, proof-backed improvement. This continuation
changes no production or main files, protocol/transcript or canonical wire.

## Complete-transaction decision

| Shape | Previous maximum | Direct-block decoder maximum |
|---|---:|---:|
| Transfer, current page | 1,070,484 | **1,069,164** |
| Transfer, rollover | 1,083,017 | **1,081,697** |
| Withdrawal, current page | 1,088,152 | **1,086,832** |
| Withdrawal, rollover | 1,101,445 | **1,100,125** |

The decoder saves **1,320 CU on each identical maximum-body proof**, with
**99,875 CU worst-observed headroom** below the real 1.2M TxV1 cap. The body is
still **40,282 bytes**. The 24 maximum-body cases, 24 ordinary-body cases and
two post-real-verifier Token-CPI-failure rollback controls pass. Tested errors,
proof hashes, protected accounts and atomic settlement match the prior build.
The unsupported rollover stale/replay cases are not counted.

Successful withdrawals retain the explicit classic SPL Token3.5 SBF; deliberate
failure controls retain their failing processor. Pool, Registry, transaction
driver and runtime settings are unchanged. The selected ELF is **1,002,168
bytes**, 96 bytes smaller, SHA256
`2d8d5a05a6ddff8f63897d0570029f1e9eaec8d1de77aaea3a1e5bf4b49226da`.

These are fixture maxima, not a universal CU bound. Same-pool selected V7
remains cheaper by **28,341 /47,296 /50,467 /51,241 CU** respectively. The
Solana testing workflow keeps the performance decision at the complete
transaction and Token/rollback boundary, not an arithmetic microbenchmark.
See [machine-readable results](decode-controls-results.json).

## What the new profile actually measured

A separate instrumented complete withdrawal-rollover proof2 costs **1,125,059
CU**, versus its quiet baseline1,101,445. It is not the optimized result above.
Across the same22 queries:

| Instrumented interval | Total CU | Per query |
|---|---:|---:|
| C1 packed decoding | 30,888 | 1,404 |
| C2 packed decoding | 17,688 | 804 |
| C1 dots plus C2 helper arithmetic | 108,202 | 4,907–4,932 |

Intervals include checkpoint/code-generation effects. The profile also records
133,411 CU between leaf hashing and internal-authentication completion. It
does not make hashing or the remaining arithmetic an irreducible lower bound.
Exact source/profile hashes and all intervals are retained in the results.

## Rejected control: fuse four C1 output channels

`fused_chunk` loads one four-value block and computes all four output channels;
`fused_dot` keeps the same seven partial reductions and balanced final sums as
the selected `fixed_dot`. Independent u128 references cover arbitrary canonical
coefficient matrices, including maximal limbs unrelated to honest power tables.
Actual packed gamma/rejection controls also pass. The previously proved
seven-chunk/range interface remains mathematically applicable per channel;
this is not a new translated-source proof.

Despite the tempting shared-load structure, the quiet complete build costs
**24,882 additional CU on every maximum-body proof**. Its worst is1,126,327 CU,
and its ELF grows2,256 bytes. It passes its 24-case maximum-body matrix, but is
**rejected for performance**. No ordinary/rollback expansion or additional
formalization was spent on this slower candidate. The increased live working
set is a plausible compiler explanation, not a measured attribution of every
extra instruction. Source-level sharing alone is not a CU forecast.

## Selected control: construct decoded blocks directly

The old decoder starts with a flat zero-filled array and overwrites every cell
in eight-value blocks. The new `decode_blocks::<13/6>` uses safe Rust
`array::from_fn` to construct all13 C1 /6 C2 blocks, then borrows the flattened
view. It does not allocate heap memory or use unsafe/uninitialized-memory code.
The four input loads, shifts, masks and canonical-value test are unchanged.
The winning fixed-width dot/helper path is unchanged; the rejected fusion flag
is **not** enabled. Short inputs fail before any input block is accessed.

[DecodeBlocks.lean](experiments/DecodeBlocks.lean) proves:

- In the block-write model, every populated flat index equals the direct
  constructor's `(index/8,index%8)` value, independent of the initial fill.
- Both index layouts visit exactly the same cells for **any check predicate**;
  no canonicality constraint is discarded.
- The literal0/8/16/23 eight-byte loads fit their31-byte blocks, and selected
  input/output indices fit the403-byte/104-limb maxima.

The arbitrary block-value function makes this a storage/index theorem, not an
assumption that received values are honest. The actual inner eight stores and
Rust array/flatten implementation are source-audited and differential-tested;
they are **not translated into Lean**. The proof establishes the stated block
model, not universal Rust/LLVM/SBF acceptance equivalence. We do not attribute
the whole measured1,320-CU difference specifically to eliminated zero stores.

Actual-source tests compare direct and old decoding on2,048 arbitrary byte
pairs, zero/all-ones input, all short/overlong lengths in the bounded range,
zero blocks, and the existing512 canonical gamma profiles. They retain rejection
of p in every one of152 packed positions and the independent maximal-limb dot
control. Full transactions provide the separate integration evidence.

Image, shifted-row, shifted-query, authentication and payment checks stay in
place. No wire field, transcript byte, query, nonce, round, mask or field is
changed. The body remains `697*16+52+24+22*621+2*296*26 = 40,282`.
No proving/search time or prover RSS was remeasured. Global recovery, full-view
adaptive privacy and resource-bounded FS retain their previous status, with
zero work credit. No production-readiness claim follows from this CU result.

## Resources, provenance and reproducibility

| Focused target | Exit | Wall seconds | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Profile SBF build | 0 | 33.57 | 590,076 KiB | 0 |
| Fused-channel optimized test/build | 0 | 20.41 | 517,056 KiB | 0 |
| Fused-channel SBF build | 0 | 33.91 | 590,716 KiB | 0 |
| Decoder optimized test/build | 0 | 20.43 | 518,600 KiB | 0 |
| Decoder SBF build | 0 | 33.79 | 591,028 KiB | 0 |
| DecodeBlocks final Lean leaf | 0 | 1.90 | 2,882,273,280 bytes | 0 |

The first small Lean preflight failed because explicit list-membership
simplification left the empty-list case. It was corrected locally, without
changing Rust or raising a cap; its failed log is separate, not proof evidence.
The final six axiom audits contain only standard `propext`, `Classical.choice`,
`Quot.sound`, with no `sorry` or new axiom in retained claimed results.
Lean4.32.0 / Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` use the pinned
Tactic cache. No unchanged proof suite was replayed.

NUC host Rust1.94.1; cargo-build-sbf2.3.0/tools1.54; optimized checked SBF
Rust1.89-dev; LiteSVM0.16.0/runtime4.2.1. Build scopes High5/Max7 GiB/jobs2;
SVM High3/Max4 GiB; all SwapMax0. All executed ELFs pass the bounded direct-r10
scan at≤4,096 bytes, with no new frame warning or unused-warning function
emitted. This is not a whole-machine stack proof. Only synthetic public
JSON/log evidence is copied back, not proof binaries or owner secrets.

`audit_gamma_fixed.py` now resolves its historical query-source blob at
`54303c98` rather than silently hashing today's edited file. Its retained JSON
reproduces **unchanged**. The new auditor replays each control's literal patch
in memory against the full starting revision, checks its measured source hash,
and verifies proof/program identities and resource/axiom logs. This preserves
historical provenance across future research edits.

On the pinned task-owned NUC copy, synchronize the research source/runners:

```sh
bash experiments/run_complete_build_nuc.sh decode-profile NEW_PROFILE_BUILD.log
bash experiments/run_decode_profile_nuc.sh NEW_PROFILE_DIRECTORY
bash experiments/run_gamma_fused_nuc.sh NEW_FUSION_TEST.log
bash experiments/run_complete_build_nuc.sh gamma-fused NEW_FUSION_BUILD.log
bash experiments/run_decode_blocks_nuc.sh NEW_DECODER_TEST.log
bash experiments/run_complete_build_nuc.sh decode-blocks NEW_DECODER_BUILD.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh decode-blocks NEW_MAX_DIRECTORY
ASPIS_V8_DECODE_BLOCKS=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
```

`experiments/` abbreviates this research directory. Remove only the max-fixture
variable for ordinary proofs. Keep the driver's1.4M CLI setting with the actual
1.2M transaction cap. For byte-exact historical sources use the retained
`decode-profile.patch` / `gamma-fused-control.patch` / `decode-blocks-control.patch`
against the starting query file (`git apply --recount`); the source hashes,
not a later flag-compatible source, identify the recorded builds.
Locally run `run_decode_blocks_lean.sh NEW_ABSOLUTE_LOG` for the changed leaf.

## Next bounded experiment

Keep the direct-block decoder; do not combine it with the rejected fusion.
The next concrete target is sorting the22 authenticated query entries. The
current `entries.sort_by_key` moves pairs of26-byte digests after hashing.
Compare sorting small `(query index, record ordinal)` descriptors first, then
constructing digest entries in that order. The quotient/rho computation must
retain the original query order; only authentication order may change.

Prove the permutation/index correspondence and retain explicit duplicate-key
rejection. Require the actual SHA backend's pure-output property before
reordering leaf calls; an arbitrary stateful callback would not suffice.
Charge descriptor storage/sorting and measure the complete build. This is a
specific prospective optimization, not a measured saving or an assertion that
all remaining opportunities have been exhausted.
