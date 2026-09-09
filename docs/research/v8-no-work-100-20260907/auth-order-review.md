# Sort descriptors before hashing: measured authentication saving

Research continuation of `8e7e177f9ef4031dc1651ccb8f779efb7681ab27`,
2026-09-09. Retain this control on top of the direct-block decoder. No main,
production default, transcript, wire or cryptographic check changes.

## Complete transaction result

| Shape | Previous maximum CU | New maximum CU |
|---|---:|---:|
| Transfer, current page | 1,069,164 | **1,065,839** |
| Transfer, rollover | 1,081,697 | **1,078,664** |
| Withdrawal, current page | 1,086,832 | **1,084,123** |
| Withdrawal, rollover | 1,100,125 | **1,097,085** |

The same maximum-body proofs save **2,562–3,325 CU** each. The worst observed
complete transaction has **102,915 CU** headroom under the real 1.2M TxV1 cap.
All 24 maximum-body cases, 24 ordinary-body cases and two post-real-verifier
Token-CPI-failure rollback controls pass with matching expected outcomes and
protected-account checks. Unsupported rollover stale/replay cases are not
counted. Maximum bodies remain **40,282 bytes**; no proofs were regenerated.

Same-pool V7 remains cheaper by **25,016 /44,263 /47,758 /48,201 CU** on the
four maxima. These are measured fixtures, not universal CU coverage or V7
parity. The Solana testing workflow keeps the decision at complete transactions
with the same Pool, Registry, pinned classic Token3.5 SBF and runtime—not a
hash/sort microbenchmark. See [exact results](auth-order-results.json).

Selected ELF: **1,002,192 bytes**, 24 bytes larger than the previous winner;
SHA256 `f06d9adaa701abba68673c340fccc038deae5691f9ac27ee0371623d6dadf44c`.

## What is proved and what changes

Previously, the callback hashed each query record in original query order,
then sorted `(index,C1_digest26,C2_digest26)` entries. The new helper sorts
22 packed u64 descriptors first: `(u64(index)<<32) | original_ordinal`.
It reads and hashes the corresponding immutable original record, constructing
the same sorted entries without sorting 56-byte digest tuples.

The ordinal breaks ties and is retained for every record; it is not replaced
by the sorted position. Gamma recombination, denominators, quotient folds and
rho injection still use the **original query order**. C1 and C2 hash inputs,
tags, salts, root comparisons, exact frontier consumption and duplicate/range
rejections are unchanged. Both branches call the same authentication routine.
No hash invocation is removed. The descriptor stack payload is176 bytes;
there is no new descriptor heap allocation and the digest-output Vec remains.
This does not attribute every measured CU to tuple moves or claim a net
whole-frame stack saving.

[AuthOrder.lean](experiments/AuthOrder.lean) proves packed index/ordinal
recovery, lexicographic order, u64 and record bounds. Its main theorem covers
**any** two weakly key-sorted permutations of the same leaf values:

- If keys repeat, the strict-key precondition fails on both paths.
- Otherwise the strictly sorted permutations are equal, and every subsequent
  authentication function receives exactly the same list.

It does not assume distinct honest queries. The actual Merkle function's
empty/depth/range/frontier/root checks remain inside the common continuation.
The model uses natural-number packing; the actual shift/or representation,
safe Rust indexing, immutable record mapping and standard sort contracts are
source-audited and tested, **not translated Rust/LLVM/SBF refinements**.

The hash backend condition is substantive: hashing a record must be a pure
function of its preimage, not of invocation order. The selected host function
constructs a new SHA state for each call; the selected SBF backend uses the
pinned `sol_sha256` implementation, whose per-call hasher is independent.
Reuse the inspected sources in
[runtime-source.json](evidence/merkle-input/runtime-source.json).
The new negative test demonstrates failure for a stateful callback. We do not
claim equivalence for every value inhabiting Rust's `HashFn` function type.
Metering still charges each call; changing when a hash is performed does not
change the transcript or provide a new Fiat–Shamir oracle query.

Optimized actual-source tests compare exact sorted leaf tuples for all720
permutations of six keys, all729 length-six schedules over three keys (also
checking actual duplicate rejection), lengths0..22, u32-max keys, 1,024
arbitrary q22 schedules and short/oversized input shapes. Synthetic records
differ by ordinal. Actual parser/packed-canonicality checks remain before
the helper in the selected callback. Outside its private caller contract, the
new helper's added guards are not a claimed equality to an old panicking API.

This is an evaluation-order optimisation, not removal of soundness checks.
All repaired image/row/query/semantic checks, masks and nonce selection powers
remain. Global extraction, adaptive full-view ZK and resource-bounded FS retain
their prior status, with zero work credit. No new public message is introduced:
`697*16+52+24+22*621+2*296*26 = 40,282`.

## Evidence and reproduction

| Focused target | Exit | Wall seconds | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Optimized source test/build | 0 | 33.41 | 560,452 KiB | 0 |
| Complete SBF build | 0 | 33.94 | 590,920 KiB | 0 |
| Final AuthOrder Lean leaf | 0 | 3.11 | 2,873,344,000 bytes | 0 |

Compilation dominates the NUC focused jobs. Build scopes High5/Max7 GiB/jobs2;
SVM High3/Max4 GiB; all SwapMax0. NUC Rust1.94.1,
cargo-build-sbf2.3.0/tools1.54, checked optimized SBF Rust1.89-dev,
LiteSVM0.16.0/runtime4.2.1 are unchanged. The actual executed ELF has no new
frame warning and its bounded direct-r10 scan is≤4,096 bytes at entry/panic;
this is not a whole-machine stack proof. No prover/RSS/search rerun occurs.

Lean4.32.0/Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` use the pinned
Tactic cache. Six final axiom audits contain only standard `propext`,
`Classical.choice`, `Quot.sound`. A local preflight failed because the
`List.Pairwise.imp` element arguments are implicit; the two extra lambda
binders were removed. The failed log is separately retained, not claimed
proof evidence. No memory cap increase, new axiom, retained `sorry` or
unchanged full Lean replay was used.

The auditor reconstructs the measured callback from its literal patch against
the full starting revision, checks source hashes against test evidence, and
checks proof/ELF/Pool/Registry/Token identities. `audit_leaf_record.py` now pins
its old callback blob at `7ccf84a3b8c66c30a9db96fb9cb305849b65106b` instead of
hashing a subsequently edited callback. Prior retained results reproduce
unchanged. Only synthetic public JSON/log files are retained, no secret or
proof-binary uploads.

```sh
bash experiments/run_auth_order_lean.sh NEW_ABSOLUTE_LOG
# On the pinned task-owned NUC copy with prior overlays:
bash experiments/run_auth_order_nuc.sh NEW_TEST_LOG
bash experiments/run_complete_build_nuc.sh auth-order NEW_BUILD_LOG
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh auth-order NEW_MAX_DIRECTORY
ASPIS_V8_AUTH_ORDER=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
python3 experiments/audit_auth_order.py
```

`experiments/` abbreviates this research directory. Remove the max-fixture
variable for ordinary proofs. Keep the driver's1.4M CLI setting and the actual
1.2M transaction cap. Use the retained callback patch against the starting
revision for exact historical source; do not assume later flag-compatible
source yields the same ELF.

## Next bounded target

The four denominators in one circle fibre are `a ± bx ± cy`. Their QM31-to-CM31
norms are quadratic in base-field x/y. Instead of computing eight independent
CM31 squares per fibre, test precomputing the norm's five circle-reduced
coefficients once and evaluating all four sign variants together. Preserve
every zero-denominator/norm check and the exact inverse outputs. First prove
the quadratic identity and test arbitrary chords—including legal zero field
coordinates—then measure the complete build. The amortised coefficient work,
added live state and existing tower batch may outweigh the arithmetic saving;
reject it if the matched SBF result regresses. This is a new hypothesis, not a
repeat of the already rejected generic QM31 batch inversion.
