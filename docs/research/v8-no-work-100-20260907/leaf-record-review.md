# C2 record hashing: a small proved and measured saving

Continuation of `74f9b7661bad35374744b04a642ac1ccbb0d3580`, 2026-09-09.
Research only; production/defaults, main, proof grammar and transcript unchanged.

## Decision and complete-transaction measurements

Retain the contiguous C2 record helper: **88 CU saved on every one of twelve
identical maximum-body proofs**, additional to the preceding Merkle savings.

| Complete shape | Previous Merkle maximum | C2 record maximum |
|---|---:|---:|
| Transfer, current page | 1,070,572 | **1,070,484** |
| Transfer, rollover | 1,083,105 | **1,083,017** |
| Withdrawal, current page | 1,088,240 | **1,088,152** |
| Withdrawal, rollover | 1,101,533 | **1,101,445** |

Worst observed headroom is **98,555 CU** below the real 1.2M TxV1 cap.
All 24 maximum-body cases, 24 ordinary-body cases and two intentional
post-real-verifier Token-CPI-failure rollback controls pass. Outcomes and
protected-account preservation match the previous build. Successful withdrawals
use the same explicitly pinned classic SPL Token3.5 SBF, not a native builtin.
The failure controls retain their intentional failing processor. Unsupported
rollover stale/replay cases are not counted.

These remain fixture maxima, not a universal CU bound. The same-pool selected
V7 is still cheaper by **29,661 /48,616 /51,787 /52,561 CU** respectively.
The selected ELF shrinks by 32 bytes to **1,002,264 bytes**, SHA256
`518049ef9d20a674dd7bc933104b89928f88b7ee7093e5f6c381474bff175b48`.
No new heap, proof field, transcript call, nonce, round or hint is introduced.
See [exact results](leaf-record-results.json). The Solana testing workflow keeps
the comparison at the complete-transaction boundary, including atomic settlement.

## Why it is the same check

The actual 621-byte query record is `C1[403] || C2[186] || salt[32]`.
The old C2 hash receives three slices of lengths `[2,186,32]`:
`[0x10,0xf1]`, `record[403..589]`, `record[589..621]`.
The new path uses the existing `private_leaf_hash_record` helper with two
slices `[2,218]`: the same prefix and `record[403..621]`.
Both hash exactly 220 bytes and truncate SHA-256 to the same 26 bytes.

C1 hashing is unchanged: its value is **not** contiguous with its salt.
The canonical packed-leaf gamma check still precedes both leaf hashes in
`opened_values_prepared`. Record length is fixed by the existing body parser;
the helper is not an alternative parser. The reference query path retains the
old C2 hash for differential comparison. Without `v8_leaf_record`, the old
measured query path remains selected.

The pinned SHA backend hashes concatenated bytes, as inspected in the preceding
[Merkle source audit](merkle-input-review.md). An arbitrary segmented `HashFn`
need not have this property. No collision assumption establishes byte equality.
The runtime syscall charges are **204 CU in either case**:
`85 + max(10,2/2) + 186/2 + 32/2 = 85 + max(10,2/2) + 218/2`.
There are still 22 C2 leaf calls. The measured difference is descriptor/
instruction work, not fewer hashes or a cheaper authenticated message.

## Formal and source evidence

[LeafRecord.lean](experiments/LeafRecord.lean) proves, for every byte list of
length621, the equality of the **literal offset slices**, transports it through
any flat-string hash, proves the 220-byte preimage length and q22 record-index
bounds, and checks the exact syscall cost. It uses the symbolic
`List.drop_take_append_drop` identity, not concrete byte enumeration.
The Rust slice correspondence is inspected and tested, not an Aeneas translation.

Optimized Rust tests execute the actual helper and parser. A capturing hash
checks raw bytes, descriptor widths and reference SHA results over every
single-position/value input and 1,024 fixed arbitrary records. Parser controls
exercise every allowed frontier length, short/overlong/misaligned bodies and
a noncanonical fixed field. The parser test does **not** claim to establish
packed-leaf canonicality; the unchanged gamma check owns that obligation.

| Evidence | Actual scope |
|---|---|
| Kernel-checked Lean | Universal slice/flat-hash identity and index bounds |
| Actual Rust helper/parser tests | Exact bytes and tested rejection boundaries |
| Complete SBF transactions | Measured accepted/rejected paths and atomic settlement |
| Full translated verifier equivalence | Not claimed |

Image/row/query/semantic checks are untouched. Earlier global recovery,
full-view adaptive ZK and resource-bounded FS obligations are unchanged; this
rewrite supplies no security bits and uses zero grinding credit.

## Resources and reproduction

| Focused job | Exit | Wall seconds | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| LeafRecord Lean | 0 | 11.68 | 2,866,020,352 bytes | 0 |
| Optimized checked tests, including compile | 0 | 36.88 | 558,640 KiB | 0 |
| Complete SBF build | 0 | 37.63 | 589,824 KiB | 0 |

Lean4.32.0 / Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` reuse the
verified local cache. Five axiom audits contain only standard `propext`,
`Classical.choice`, `Quot.sound`; no `sorry` or new axiom. Source/olean hashes
and raw logs are retained. No unchanged Lean suite was replayed.

NUC build scopes use High5/Max7 GiB/jobs2; SVM High3/Max4 GiB; all SwapMax0.
Host Rust1.94.1, cargo-build-sbf2.3.0/tools1.54, checked optimized SBF Rust1.89-dev
and LiteSVM0.16.0/runtime4.2.1 match the prior build. The executed ELF's direct-r10
scan reports maximum4,096 at entry/panic labels, no unused warning function
emitted, and no new frame warning. This is not a whole-machine stack proof.
No proving/search time or prover RSS was remeasured.

The body remains `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes.
Only synthetic public JSON/logs are archived, not proof binaries or recovered
secrets. No RPC, deployment or production modification occurs.

Locally: `bash experiments/run_leaf_record_lean.sh NEW_ABSOLUTE_LOG`.
On the pinned task-owned NUC copy after the winning Merkle overlay, synchronize
the changed research callback/helper/runners, then:

```sh
bash experiments/run_leaf_record_nuc.sh NEW_TEST.log
bash experiments/run_complete_build_nuc.sh leaf-record NEW_BUILD.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh leaf-record NEW_MAX_DIRECTORY
ASPIS_V8_LEAF_RECORD=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
```

`experiments/` abbreviates this research directory. Remove only the max-fixture
variable for the ordinary matrix. Keep the driver's 1.4M CLI setting with its
separate actual1.2M cap. `audit_leaf_record.py` checks retained results against
the committed Merkle winner without heavy replays.

## Next bounded experiment

Next split the current canonical/gamma interval into **packed decoding versus
field dot products** in one instrumented complete execution. Fixed-width gamma
is already installed. Inspect emitted decoder bounds/loop work before another
specialization. It must retain all152 canonicality checks and arbitrary
malicious packed inputs, then improve the quiet complete build. Do not count
the existing four-load unpacking, prepared powers or partial reductions again.
This targets a larger remaining interval rather than claiming all useful
optimizations have been exhausted.
