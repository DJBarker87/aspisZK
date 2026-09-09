# Merkle inputs: fewer copies, identical authenticated bytes

Research continuation of `54303c98ef06ba8ea72d3456c738fcb51a362796`,
2026-09-09. No production source/default, main, proof representation or
transcript is changed. The implementation is an isolated NUC source overlay.

## Measured decision

| Complete shape | Prior gamma-fixed maximum | Selected combined maximum |
|---|---:|---:|
| Transfer, current page | 1,083,060 | **1,070,572** |
| Transfer, rollover | 1,095,606 | **1,083,105** |
| Withdrawal, current page | 1,100,739 | **1,088,240** |
| Withdrawal, rollover | 1,114,035 | **1,101,533** |

The combined rewrite saves **12,472–12,502 CU on identical complete maximum-body
proofs**, with **98,467 CU** worst-observed headroom below the real 1.2M TxV1
cap. Each shape uses three predetermined archived **40,282-byte** proofs,
actual Registry/account authentication and atomic Pool settlement. Successful
withdrawals use the explicitly pinned classic SPL Token3.5 SBF.

All three implementation controls pass their 24-case maximum-body matrix.
The winning combined version also passes 24 ordinary-body cases and two
deliberate post-real-verifier Token-CPI-failure rollback cases. Malformed proof,
wrong-release, stale-lane and replay results agree with the prior build, and
protected accounts remain unchanged. The failing-CPI controls retain their
intentional failure processor. The driver's unsupported rollover stale/replay
cases are not counted. There is no diagnostic runtime-limit override.

| Control | Same-proof savings over gamma-fixed | Worst observed CU | ELF change |
|---|---:|---:|---:|
| Three parent-input slices only | 2,304 | 1,111,731 | −488 bytes |
| Borrow digests, contiguous parent input | 8,123–8,153 | 1,105,882 | −320 bytes |
| **Both changes together** | **12,472–12,502** | **1,101,533** | **−952 bytes** |

The combined saving is **not** the sum of the two standalone savings; it was
measured as a complete build. Retain both. The same-pool V7 control remains
cheaper by **29,749 /48,704 /51,875 /52,649 CU** respectively. These are fixture
maxima, not universal CU coverage or matched-V7 parity.

See [machine-readable results](merkle-input-results.json) for every proof,
artifact, outcome and comparison. The Solana testing workflow keeps this at
the complete-transaction boundary with the same Token/runtime configuration,
rather than extrapolating a hash microbenchmark.

## What changed

The existing parent preimage is exactly `0x11 || left26 || right26`. The first
control supplies the same string as three slices instead of copying it into
a fresh 53-byte array. The second control borrows the immutable C1/C2 digests
from the current level and frontier byte slices instead of copying them into
local 26-byte arrays. The parent-output values are still materialized and
pushed into the next level as before.

Both retain the same independent SHA-256 calls, first-26-byte truncation,
domain byte, child order, sorted-index checks, depth/length guards, exact
frontier-consumption check and root comparisons. No Merkle evidence is omitted.
The public two-tree traversal was already shared; this does not count that old
saving again. The maximum-body q22 shape still uses **634 internal hashes**.

The copy buffers are redundant data representations, not security checks.
The source remains safe Rust. Immutable borrows end before the level/scratch
swap; no unsafe alias, untrusted hint, unchecked offset or new allocation is
introduced. The old code remains selectable when the research flags are absent.

## The exact equivalence boundary

[MerkleInput.lean](experiments/MerkleInput.lean) models the concrete three buffer
ranges with finite byte vectors, proves that their 53-byte buffer equals the
flattened slice list, proves its length, and transports equality through **any
hash of that flat byte string**. It also checks the pinned syscall-cost delta.
The proof uses symbolic `Fin.append`/`List.ofFn` rewrites, not enumeration of
the byte alphabet or giant generated expressions.

There is an important API distinction: an arbitrary Rust `HashFn` could observe
the number of slices. The Rust function type alone does not guarantee the
equivalence. A permanent negative test demonstrates that counterexample.
The inspected selected backends do hash the concatenation:

- Host `solana-sha256-hasher2.3.0::Hasher::hashv` feeds each slice to one SHA state.
- SBF `solana-sha256-hasher2.3.0::hashv` calls `sol_sha256`; the pinned
  `solana-syscalls4.2.1::SyscallHash` translates each slice and feeds its bytes
  to one hasher, without hashing lengths or segmentation delimiters.

This is a source audit of the actual backend, not a new probabilistic primitive
assumption. Runtime slice/memory validation remains; all new descriptors point
to live, correctly sized immutable Rust values. The implementation tests
capture and compare the **raw concatenated input**, independently of comparing
SHA outputs, for 14,336 parent pairs per build. They cover every single-byte
position/value and 1,024 deterministic arbitrary pairs.

An independent full-tree/frontier constructor exercises all **255 nonempty
depth-three query schedules**, malformed frontier lengths/bytes, altered leaves,
duplicate entries and empty schedules. All four focused source tests pass in
each of the three builds. These finite controls are not a universal Rust
translation or a soundness probability experiment.

| Evidence | Scope |
|---|---|
| Lean byte-vector theorem | Universal equality of the modeled parent strings and flat-string hashes |
| Backend source inspection | Selected host/syscall hashing consumes concatenated bytes |
| Safe borrowed traversal and Rust controls | Same input bytes, roots and tested malformed behaviour in the actual module |
| Complete SBF matrices | Measured accepted/rejected transactions and atomic settlement |
| Full Rust/LLVM/SBF refinement | **Not claimed** |

No image, row, query, semantic or ownership check changes. Security gets zero
work credit; global recovery, adaptive full-view ZK and resource-bounded FS
retain their previous status. This rewrite does not supply missing security bits.

## Why it saves despite a more expensive syscall

The pinned runtime charges `85 + sum(max(10, floor(slice_length/2)))` for these
SHA calls. The old `[53]` input costs **111 CU** inside the syscall; `[1,26,26]`
costs **121 CU**. Thus the maximum-body schedule pays **6,340 additional syscall
CU**, before instruction and buffer costs. The measured complete build still
saves CU because the removed copy/instruction work outweighs it. There is no
claim that a wider hash output, fewer hashes, or faster host JIT caused the gain.

The exact inspected dependency hashes/sections are in
[runtime-source.json](evidence/merkle-input/runtime-source.json). The cost model
explains one component only; the complete SBF comparison decides the result.

## Resources and reproduction

Focused Lean4.32.0 / Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`:
exit0, **4.29 s**, **2,864,431,104-byte RSS**, zero swaps. The final four axiom
audits contain only standard `propext`, `Classical.choice`, `Quot.sound`, with
no retained `sorry` or new axiom. The first local leaf preflight used a broad
simplifier which expanded the 53 concrete cells before the append rewrite;
it failed without memory pressure and was replaced symbolically. Its failed
log is archived separately, not treated as a proof success. A harmless unused
simp-argument warning remains in the successful log.

| NUC command | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Slices optimized test/build | 0 | 25.00 | 599,484 | 0 |
| Borrow optimized test/build | 0 | 24.68 | 601,800 | 0 |
| Combined optimized test/build | 0 | 24.76 | 596,948 | 0 |
| Slices complete SBF build | 0 | 34.11 | 590,824 | 0 |
| Borrow complete SBF build | 0 | 34.06 | 589,892 | 0 |
| Combined complete SBF build | 0 | 33.67 | 590,076 | 0 |

Build scopes use High5/Max7 GiB/jobs2; SVM uses High3/Max4 GiB. Every scope has
`MemorySwapMax=0`. NUC host Rust1.94.1, cargo-build-sbf2.3.0/tools1.54,
checked optimized SBF Rust1.89-dev and LiteSVM0.16.0/runtime4.2.1 are unchanged.
No package-wide Lean replay, deployment, paid job or fresh prover run occurs.

Selected ELF: **1,002,296 bytes**, SHA256
`2689a06875d429fd5c1e81cff6791ec183ef267b01b81f76af123289a6f6953b`.
All three emitted-code audits report maximum direct-r10 offset4,096 at the
entry/panic labels, with no new SBF frame warning. This is not a whole-machine
stack proof. The patched Merkle source SHA256 is
`10e0fd6242034b59d43db57e6a4a83c946ba8a1c0917943877b3ccbda6df376b`.
The preparer requires the exact prior source hash before applying the overlay.
Other program/runtime hashes are unchanged and checked in the results.

No extra heap, proof field, transcript byte, nonce or round is added:
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes`.
Proving time, search latency and proving RSS are not remeasured. Archived
evidence contains synthetic public logs, not proof binaries or owner secrets.

Locally run `run_merkle_input_lean.sh NEW_ABSOLUTE_LOG` for the changed leaf.
On the pinned task-owned NUC source copy after the gamma-fixed overlays:

```sh
bash experiments/run_merkle_input_nuc.sh prepare NEW_PREPARE.log
bash experiments/run_merkle_input_nuc.sh both NEW_TEST.log
bash experiments/run_complete_build_nuc.sh merkle-both NEW_SBF.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh merkle-both NEW_MAX_DIRECTORY
ASPIS_V8_MERKLE_BOTH=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
```

`experiments/` abbreviates this research directory. Remove only
`ASPIS_COMPLETE_MAX_FIXTURES` for the ordinary matrix. Replace `both`/
`merkle-both` with `slices`/`merkle-slices` or `borrow`/`merkle-borrow` for the
separate controls. Retain the driver's 1.4M CLI runtime setting with the separate
actual 1.2M transaction cap. `audit_merkle_input.py` checks retained results,
source/proof hashes and resource logs without replaying unchanged suites.

## Next bounded experiment

Keep the combined version. One concrete remaining duplication is the **C2 leaf
slice descriptor**: its 186-byte value and following 32-byte salt are already
contiguous at query-record bytes403..621. The existing
`private_leaf_hash_record` helper can hash that record with two slices instead
of three, preserving `0x10 || C2_tag || value || salt`. C1 cannot use this same
shortcut because its value is separated from the salt by C2. Prove the actual
record partition, test malformed boundaries, and compare a complete SBF build.
Reject it if descriptor/call changes do not improve measured CU; do not infer
the saving from slice count. Larger future savings still need measured targets,
not a claim that all optimization opportunities have been exhausted.
