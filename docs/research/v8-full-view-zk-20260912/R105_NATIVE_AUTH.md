# R101–R105: measured authentication profile and fixed-field parsing

Base: `d3775d029b91b16a3a6b34ca9c84d3aa7ae08690`, 2026-09-30.
Research branch `research/v8-r64-guarded-m31-20260929`.
**Neither under-1M execution nor full security is achieved.**

## Complete verifier results

| Experiment | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| Pushed R99 control, binary authentication | 1,123,090 | 1,121,361 | Preserved control |
| R102, versioned eight-way authentication | 1,072,399 | 1,072,158 | Retain research profile |
| R103, word-encoded leaves on R102 | 1,080,902 | 1,078,242 | Reject |
| R104 aligned word reads, on R103 | 1,076,876 | 1,074,216 | Reject against R102 |
| R104 bounded inactive sums, on R102 | 1,074,919 | 1,074,649 | Reject |
| R105 fixed-field parser, on R102 | **1,066,127** | **1,065,886** | Retain research implementation |

The selected research endpoint saves **56,963 / 55,475 CU** against the pushed
control. The larger fixture remains **66,127 CU above 1M**. Both actual honest
runs at the 1,000,000 cap still exhaust; the completed results above use the
diagnostic cap. Resource exhaustion is not rejection. Corrupted combined
finals reject with Custom(6) at both caps. Heap remains 262,144 bytes and the
simulated accounts are unchanged. These are complete verifier-only executions,
not settlement executions, a universal resource bound, or production approval.

R102 and R103 change the research profile and regenerate genuine proofs for
the same two witnesses. R104 and R105 reuse their stated parent's exact proof
bytes. R105 uses R102, **not** either rejected word-leaf or inactive-sum build.
R83 remains the old-profile control; R84 and its descendants are unpromoted.

## Authentication pilot, then actual source integration

The preceding R101 benchmark uses independent full public synthetic trees and
the same 22 indices across arities, including entry/frontier parsing. It is
**authentication only**, not an Aspis proof execution or actual q22 replay:

| Arity | World 0 CU | World 1 CU | Authentication input bytes |
|---|---:|---:|---|
| 2 | 114,620 | 118,920 | 15,136 / 15,708 |
| 4 | 76,768 | 79,451 | 21,740 / 22,520 |
| 8 | 66,854 | 70,587 | 31,880 / 33,700 |

All six honest inputs pass at both caps. Changed roots reject with Custom(101),
not resource failure. The independent host gate covers 768 honest cases and
8,163 malformed cases. These numbers were not subtracted from the control to
manufacture a full-verifier result; R102 was subsequently built and measured.

R102 retains SHA-256, 26-byte digests, 22 queries, both commitment trees, the
original packed leaf encoding, salts, field/challenge sizes, and commitment
chronology. It uses six eight-way levels with parent domain `0x18` and an
explicitly distinct transcript profile. The verifier hashes borrowed child
slices; the independent host prover/reference concatenates parent bytes and
reconstructs the tree separately. Sorted/unique/in-range indices, equal
frontier lengths, exact frontier consumption, and both root equalities remain.

The exact maximum frontier is **658 digests per tree**, giving a maximum body
of **59,138 bytes**. An executable schedule attains it. Each measured proof is
57,682 bytes. R102's actual-source prover/reference gate checks 512 schedules
and 42,772 honest/malformed comparisons. Its full host gate has 3,283 cases:
one acceptance and 3,282 checked rejections, including two old profiles.

Both newly generated prefixes pass the actual opposite-witness C1/H1/G
correction gates: H1 rank 540, G's 626-equation system rank 602, p0/p2 retained,
all seven first-relation coefficients and combined Final256 retained. The
source helper is rebuilt and the original equations are checked independently.
**These are two fixed-prefix certificates, not universal affine coverage or
causal full-transcript privacy.**

## Native candidates and early rejection

R103 replaces only the leaf representation with canonical little-endian
32-bit limbs (C1 416 bytes, C2 192), a new leaf domain `0x20`, and another
explicit profile. Every incoming limb is checked, including beta zero/one.
The primary hashes the original word bytes; only the independent reference
repacks into the retained 31-bit arithmetic oracle. Old packed decoders and
negative sources are retained. Both actual-source witness gates pass again.
There are 4,096 arithmetic comparisons, 3,201 malformed controls, 2,048
encoding round trips, and 13,316 full-wire cases. The fixed record increase is
418 bytes; actual total sizes also vary with the changed sampled frontier.
This candidate is slower and is not selected.

R104's word-reader follow-up uses `align_to::<u32>()` only on little-endian
targets and only when both alignment fragments are empty. Every bit pattern
is valid for u32; canonical field validation still follows. Unaligned and
big-endian input retains the byte decoder. Four offsets are checked. It saves
4,026 CU against R103 but remains slower than R102, so it is also rejected.

The separate R104 inactive-sum candidate verifies the fixed integer map and
subset uniqueness, validates canonical input limbs, accumulates bounded u64
sums, and reduces once per output. It passes 77,824 scalar comparisons and
1,536 malformed cases, the actual compact-source comparison, and full runtime.
Nevertheless it adds about 2.5k CU. The guarded old path remains in its source;
the entire candidate is rejected. No algebraic operation count is called a CU
saving, and no formalization campaign was started for the losing kernel.

R105's selected fixed-field parser applies alignment-checked u32 reads to
the **existing** 699-field header, without changing bytes or profile. A bounded
aggregate invalid-bit check rejects every limb at least P. No hashing or
semantic processing occurs until validation finishes. Misaligned/big-endian
inputs keep the original decoder. It passes 896 accepted comparisons and
33,645 malformed cases, including every fixed-field limb at four offsets and
P, 2^31 and u32::MAX. The complete host wire gate still has 3,281 checked
rejections plus the honest control. The exact full-execution saving against
R102 is **6,272 CU on each fixture**.

A separate Copy-registry coalescing candidate proves exact integer coefficient
equality and passes the retained 70,720 selector-weight checks and 512 complete
lane comparisons. It finds **544 terms before and 544 after**. The premise of
that experiment—duplicate terms removable at this boundary—is false. It was
stopped after host checks, without an SBF build or a claimed CU result.

## Trace, evidence and security boundary

The R102 instruction trace matches its clean ELF text and exact 1,072,399 CU.
It contains 997,803 instructions: 189,554 loads, 115,251 stores and 65,272
integer multiplies. These are exclusive instruction counts for that build,
not a profile of R105 or additive inclusive-region CU measurements. Raw
register data remains on the NUC.

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r105_evidence.py
```

The 199-artifact public evidence manifest pins all seven stages, their source
deltas and immediate parents, commands, runtime receipts, resource caps,
wall time/RSS/swap logs, fixtures by hash/size, and ELF hashes. No fixture
contents, ELFs, raw register files or wallet keys are collected. All heavy
jobs use the Tailscale NUC, cached optimized Rust builds, explicit memory
high/max caps and zero task swap. Concurrent caps stay below 26 GiB. No
unchanged full formal replay was run; **there are no new Lean targets here**.
The Solana skill's source, malformed-input, stack and complete-runtime gates
continue to govern selection.

The first security proposition is still **universal actual-source C1/H1/G joint
affine-image compatibility for the two-swap sparse-G profile**, including
p0/p2 and every legal adaptive/degenerate prefix, or source-justified
exceptional-event losses. The new eight-way profile additionally requires
commitment binding/hiding and exact-source oracle composition. The separately
compiled sampler observer theorems are unchanged; they do not supply this
whole-experiment composition automatically.

Full causal posterior simulation, seed expansion/C2/shared-oracle composition,
visible failures/retries/publication, and coherent original quotient-pair
extraction **before beta** remain open. No new hiding assumption, reduced
query count, shortened field/challenge/digest, deleted C1/H1 negative, production
promotion, deployment, wallet operation or settlement execution is used.
The work is not complete merely because the remaining CU gap is smaller.
