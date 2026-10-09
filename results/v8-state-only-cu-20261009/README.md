# M2: Rate256/q22 Rust reference verifier CU

**1,125,014 verifier CU — unmined diagnostic path (PoW rejection disabled).**
Five identical release SBF runs accepted; simulation and execution agree on
status, CU and every log. Both M1 and M2 have a single-byte opened-leaf
rejection witness under the same diagnostic tag used for their acceptance runs.

This is a **shape-only measurement of the Rust reference**, not a measurement
of an implementation established to refine the proved model. R1's structural
correspondence obligation remains open:

| Dimension | Measured Rate256 Rust reference | Proved-model target described in R1 |
| --- | --- | --- |
| Width | 28 columns | 29 lanes |
| Opening protocol | Four arity-four FRI folds | One fold |
| Evaluation points | 2^18 | Does not by itself identify the query universe |
| Sampled query universe | 2^16 fibres (four points per fibre) | `Fin (2^18)` |
| Queries | 22 | 22 |

The four-point grouping does **not** establish a conservative abstraction.
R1 must determine whether a refinement argument transfers the model's bound,
or whether the real protocol requires a new soundness derivation. **Neither
model correspondence nor the q22/9557 budget is established by M2.** No Lean
or research-document changes are part of these commits.

Base: `7fcda8577`; measured source:
`5e2b0270cd517f74b548859bf9f72308f44197a7`.
New profile ID **24**, log blowup **8**, q**22**, batch grinding **36**, fold
work **[39,35,31,27]**, final work **36**. The shared maximum remains **36**
to preserve Rate16/q36 and Rate32/q29, as explicitly agreed. Opening depths
are **16 / [14,12,10]**. Trace rows, field, four-fold count, final-polynomial
length, lane selection, degrees, candidate bound and fallback code are unchanged.

## Side-by-side measurements

**All V8 numbers below: unmined diagnostic path (PoW rejection disabled).**
These are verifier-only CU, including account/public parsing and checkpoint
logging. The M1 row preserves its original ELF and fixture; it was not rerun
for acceptance under the new binary.

| Shape | Queries | Proof bytes | Verifier CU | Headroom to 1.3M | Headroom to 1.4M | Signed verifier-only TxV1 proposal bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| M1 Rate512, atomic v3 | 16 | 54,604 | 987,814 | 312,186 | 412,186 | 444 |
| **M2 Rate256, atomic v3** | **22** | **68,364** | **1,125,014** | **174,986** | **274,986** | **444** |
| M2 minus M1 | +6 | +13,760 | +137,200 | −137,200 | −137,200 | 0 |
| V7 historical strict Tag-73 comparison | 16 | not specified at cited anchor | 1,084,738 | 215,262 | 315,262 | 1,043 |

V7's explicit comparison is **1,084,738 verifier / 1,218,972 transaction CU**,
from [the historical cutoff measurement](../../docs/research/v7-first-cap203-scan-cu-fix-20260902.md#cutoff-measurement)
(lines 82–83), not rerun here. M2 is 40,276 verifier CU above that V7 figure;
profiles and workloads differ, so this is not a like-for-like speed comparison.

| Phase | M1 Rate512/q16 CU | M2 Rate256/q22 CU | M2 − M1 CU |
| --- | ---: | ---: | ---: |
| Transcript / sumcheck replay | 140,757 | 141,511 | +754 |
| Terminal excluding mask | 272,768 | 272,758 | −10 |
| Mask terminal | 13,945 | 13,915 | −30 |
| Relation / final polynomial | 149,891 | 149,914 | +23 |
| Merkle / opening authentication | 176,047 | 227,197 | +51,150 |
| FRI query arithmetic | 231,316 | 316,613 | +85,297 |
| Account/public parsing, return, other checkpoints | 3,090 | 3,106 | +16 |
| **Total** | **987,814** | **1,125,014** | **+137,200** |

Terminal including mask is 286,673 CU for M2 (M1: 286,713; delta −40).
All finer terminal checkpoint deltas are retained in each run JSON.
Opening authentication and FRI query arithmetic account for **136,447 CU,
99.45% of the increase**. FRI query arithmetic is now the largest individual
interval (28.14%); the whole terminal is 25.48%, opening authentication 20.20%,
and relation/final-polynomial arithmetic 13.33%. The isolated mask terminal
is 1.24%. Cost growth sits in the query-dependent PCS work, not the mask terminal.
The Merkle interval includes decoding and bookkeeping, and the terminal and
transcript mix hashing and arithmetic; these checkpoints do not isolate the
cost of every hash from every field operation. The profiles also change
domain size, profile binding and transcript-derived queries, so the phase
delta is not a controlled per-query marginal cost.

M2 fits one verifier-only instruction at the runtime limit. It does not force
a two-transaction split for this measured reference path. A decision for the
proved/refined protocol or a complete Pool transaction remains open. **No
transaction-level CU for Pool CPI, receipts, settlement, proof upload or
network execution is measured.** The harness total (1,125,370 CU) contains
only the diagnostic verifier plus compute-budget/heap overhead. TxV1 itself
was serialized, not executed. Its 444 bytes leave **3,652 bytes** of the 4,096
budget; the 68,364-byte proof is in a **68,404-byte sealed ASPU account**,
with 216 public-input bytes and a 217-byte instruction.

## Rejection witnesses and PoW allowance

- **M1** [rate512-q16-reject-1.json](rate512-q16-reject-1.json): the original
  measured ELF rejects byte offset 6,738, 52 → 53 in the first opened C1 leaf,
  at **628,047 verifier CU — unmined diagnostic path (PoW rejection disabled)**.
  This run completed before adding the new shape.
- **M2** [rate256-q22-reject-1.json](rate256-q22-reject-1.json): the M2 measured
  ELF rejects byte offset 6,738, 171 → 170 at **643,656 verifier CU — unmined
  diagnostic path (PoW rejection disabled)**. The changed limb is 1,471,045,034,
  still canonical.

Both are exactly one changed byte, both reach relation/final-polynomial
completion and fail opening authentication with
`InstructionError(2, InvalidInstructionData)`. Simulation and execution agree
and the sealed proof account is unchanged. Neither is a CU-limit rejection.

The new ELF has its own [PoW disassembly audit](rate256-q22-pow-omission-audit.json).
Strict replay logically checks six SHA-256 hashes of 41 bytes (32+1+8) and
six 64-bit threshold comparisons. The diagnostic binary **already performs
all six hashes and two comparisons**; enabling rejection adds **zero hashes
and four comparisons**, bounded by **24 ordinary SBF instructions / 24 CU**.
The resulting accounting allowance is **1,125,038 verifier CU — unmined
diagnostic path (PoW rejection disabled), plus static PoW allowance**. This
bounds the omitted check logic for this compiled replay, not a mined-proof
total: mining changes the transcript and queries. Strict native verification
rejects the unmined fixture with `BatchGrindingRejected`.

## Verification-crate change inventory

**No algorithmic verification changes beyond shape plumbing were required.**
The full inventory, including tests, is:

| File | Change and reason |
| --- | --- |
| `aspis-core/src/state_only_prefix.rs` | Add profile 24 constants/shape and header recognition; extend existing header/schedule tests to it. Shared capacity stays 36; transcript logic is unchanged. |
| `aspis-core/src/circle_line_merkle.rs` | Add the four-fold geometry for the smaller domain. |
| `aspis-core/build.rs` | Add domain log 18 to the existing table generator; formulas are unchanged. |
| `aspis-core/src/circle_openings.rs` | Select the six Rate256 tables at layer-zero depth 16 in both geometry dispatches; authentication and transition algorithms are unchanged. |
| `aspis-core/src/circle_fri.rs` | Tests only: compare generated Rate256 tables to random-access coordinate arithmetic, including boundary indices. |
| `aspis-statement/src/state_only_verify.rs` | Select Rate256 geometry; allow its exact shape in the structural probe, terminal cost probe, and atomic-v3 verifier guards. |
| `aspis-prover/src/state_only_candidate_prefix.rs` | Allow the exact Rate256 shape in the atomic-v3 front builder; statement-digest equality remains mandatory. |
| `aspis-prover/tests/state_only_full_proof.rs` | Add requested release round-trip, legacy relation agreement, claim corruption and serialized corruption teeth (including opened leaf and final polynomial). |
| `aspis-prover/tests/atomic_state_only_full_proof.rs` | Add atomic round-trip, query-universe assertions, public-statement binding and eight proof-corruption checks. |

Outside those crates, the host driver now selects either profile and supports
the one-byte rejection mode. Summary/audit scripts collect evidence for each
ELF. `programs/aspis-verifier/src/dispatch.rs`, the diagnostic tag/gate and
program probe source are unchanged from M1. No optimization was attempted.

## M2 reproducibility and resources

Runs [1](rate256-q22-run-1.json), [2](rate256-q22-run-2.json),
[3](rate256-q22-run-3.json), [4](rate256-q22-run-4.json),
[5](rate256-q22-run-5.json), [fixture](rate256-q22-fixture.json),
[summary](rate256-q22-summary.json), [source manifest](rate256-q22-source-manifest.json),
[environment](rate256-q22-environment.json), and
[test/build log excerpts](rate256-q22-build-log-excerpts.json) pin the evidence.
All 339 source-manifest hashes match the build host. Runtime remains
**LiteSVM 0.16.0 / Agave 4.2.1**, with the same committed lockfile. Builder is
**Agave CLI 3.1.13 / platform-tools 1.52 / SBF rustc 1.89.0**; native
rustc/cargo **1.94.1**. All builds are optimized release builds.

Host: **nuc, dombarker@100.108.41.90**, Intel Core Ultra 7 155H, ~62 GiB RAM.
Every build/test/fixture job used a separate scope with **MemoryHigh=8 GiB,
MemoryMax=12 GiB, MemorySwapMax=0**; measurement/rejection used **4/6 GiB,
swap max 0**. Own simultaneous reservation never exceeded **24 GiB**, with
~50 GiB available before starting; all own scopes report zero swap.

| Job (resource JSON) | Exit | Wall seconds | Sampled aggregate RSS MiB | Cgroup peak MiB |
| --- | ---: | ---: | ---: | ---: |
| [Release non-atomic round-trip](rate256-q22-roundtrip.json) | 0 | 119.113 | 901.48 | 750.61 |
| [Release atomic tests (4 passed)](rate256-q22-atomic-tests.json) | 0 | 14.012 | 300.60 | 300.36 |
| [Release prefix tests (8 passed)](rate256-q22-core-profiles.json) | 0 | 18.516 | 706.51 | 581.00 |
| [Generated table check (1 passed)](rate256-q22-core-tables.json) | 0 | 0.501 | 12.94 | 54.74 |
| [Release driver build](rate256-q22-driver-build.json) | 0 | 38.040 | 958.53 | 786.95 |
| [Atomic fixture + native checks](rate256-q22-fixture-generation.json) | 0 | 13.511 | 88.53 | 89.09 |
| [Release SBF build](rate256-q22-sbf-build.json) | 0 | 21.519 | 1115.24 | 865.31 |
| [Five paired LiteSVM runs](rate256-q22-measurement.json) | 0 | 0.501 | 12.64 | 36.26 |
| [Opened-leaf rejection](rate256-q22-rejection.json) | 0 | 0.501 | 12.69 | 33.50 |

Resource records contain exact commands, caps and source revisions. The
recorder samples every 0.5 s, so the short LiteSVM jobs can finish between
samples; cgroup peaks and child `ru_maxrss` are also retained. The non-atomic
test took 85.07 s after 33.98 s compilation; no unchanged full suite was repeated.

The private build-host root is
`/home/dombarker/project-offloads/aspis-v8-state-only-cu-20261009`.
M2 artifacts are under `m2/sbf`, `m2/fixtures`, `m2/runs`, `m2/evidence`;
M1's measured ELF/fixture and keys remain retained. Its unstripped ELF is
also retained at `sbf/aspis_verifier.unstripped.so` before cache reuse.
No binaries, proof blobs or keys are committed. No network transactions were sent.

From the pinned source, these are command payloads for separate capped
build-host scopes (set `ASPIS_SOURCE_REVISION` to the measured revision):

```text
cargo run --release --locked -p aspis-xtask -- v8-state-only-cu-probe fixture FIXTURE_DIR rate256-q22
cargo run --release --locked -p aspis-xtask -- v8-state-only-cu-probe measure ELF FIXTURE_DIR RESULTS_DIR rate256-q22
cargo run --release --locked -p aspis-xtask -- v8-state-only-cu-probe reject ELF FIXTURE_DIR RESULTS_DIR rate256-q22
python3 scripts/v8_state_only_cu_summarize.py results/v8-state-only-cu-20261009 rate256-q22
```

Every Cargo/build/measurement command must run in its own capped scope
as recorded in the resource JSON. The actual recorded measurement invokes
the already-built release driver directly. The PoW audit requires the
matching unstripped ELF and measured ELF; see its script usage.

---

# M1 historical measurement (before M2 shape addition)

The profile-availability and unchanged-crate statements below describe M1's
source revision only. M2's changes and open structural obligations are above.

**987,814 verifier CU — unmined diagnostic path (PoW rejection disabled).**
All five identical Rate512/q16 runs succeeded. Simulation and execution agree
on status, CU, and every log. The measurement executes the release SBF binary
in LiteSVM; it is not a live-cluster deployment or a production acceptance claim.

Base: `dd621ba6244ec7eeb37d12d52cc72397b5ec1aae`.
Measured source: `2940f8a7321f08dfed01c2d1a0e799b58c7d2382`.
The production `dispatch.rs`, all three verification/prover crates, research
documents, and Lean trees are unchanged. No optimization was made.

## Profile identification

None of the three named shapes implements q22 over a 2^18-point evaluation
domain. With the existing 2^10 message rows, that domain would require
`log_blowup = 8` (rate 1/256). Rate512 is nearest both in query count and in
log-domain size: **six fewer queries, twice the evaluation domain, and twice
the blowup**. This result does not measure or inherit the q22 soundness bound.

All entries below are source constants, not CU measurements. “Folds” lists
the four per-round grinding difficulties.

| Shape | Profile ID | Queries | Log blowup / blowup | Evaluation points | Query fibres | Batch / folds / final grinding bits |
| --- | ---: | ---: | --- | ---: | ---: | --- |
| Requested q22, interpreting domain as evaluation points | no existing shape | 22 | 8 / 256 | 262,144 | 65,536 under the existing arity-four layout | No grinding vector specified in the request; no matching implementation to pin |
| `STATE_ONLY_RATE16_SHAPE` | 18 | 36 | 4 / 16 | 16,384 | 4,096 | 24 / [39, 35, 31, 27] / 36 |
| `STATE_ONLY_RATE32_SHAPE` | 19 | 29 | 5 / 32 | 32,768 | 8,192 | 26 / [39, 35, 31, 27] / 36 |
| **`STATE_ONLY_RATE512_SHAPE`** | **20** | **16** | **9 / 512** | **524,288** | **131,072** | **36 / [39, 35, 31, 27] / 36** |

Sources: `crates/aspis-core/src/state_only_prefix.rs:47–107` and
`crates/aspis-core/src/circle_prefix.rs:44`. The query sampler uses
`2^(STATE_ONLY_LOG_ROWS + log_blowup - 2)` **fibre indices**, rather than all
evaluation points (`state_only_prefix.rs:825–840`). If the requested 2^18
domain instead means the **query universe**, Rate512 still does not match:
its universe is 2^17. A 2^18-fibre universe would need 2^20 evaluation points
and blowup 1,024 with this layout. No security-profile equivalence is assumed.

The atomic-v3 acceptance function explicitly rejects every shape except
Rate512 (`crates/aspis-statement/src/state_only_verify.rs:799`). Therefore
Rate16 and Rate32 were not measured: an atomic-v3 scaling curve would require
changing the verification crates. The tests named in the request use the
non-atomic public statement. This fixture uses their existing completion and
masking machinery through `build_hiding_atomic_state_only_proof_v3`, with the
deterministic witness from `tests/atomic_state_only_full_proof.rs`.

## Measured table

**All V8 CU entries: unmined diagnostic path (PoW rejection disabled).**
Totals include the probe's account/public-input checks and phase logging.
Headroom is relative to the **verifier total**, not a complete Pool transaction.

| Shape | Queries | Proof bytes | Transcript / sumcheck CU | Terminal CU, including mask | Relation / final polynomial CU | Merkle / openings CU | FRI query CU | Other CU | Verifier total CU | Headroom to 1.3M | Headroom to 1.4M |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Rate512, atomic v3** | **16** | **54,604** | **140,757** | **286,713** | **149,891** | **176,047** | **231,316** | **3,090** | **987,814** | **312,186** | **412,186** |
| V7 historical strict Tag-73 comparison | 16 | not specified at cited anchor | — | — | — | — | — | — | 1,084,738 | 215,262 | 315,262 |

The explicit V7 comparison is **1,084,738 verifier / 1,218,972 transaction CU**,
from [the cutoff measurement](../../docs/research/v7-first-cap203-scan-cu-fix-20260902.md#cutoff-measurement)
(lines 82–83). Its transaction is a strict-work SPL-withdrawal rollover with
255 populated pairs and a 1,043-byte TxV1. It was not rerun here. The V8
verifier figure is 96,924 CU lower, but the profiles, workloads, and measurement
instrumentation differ; this is not a like-for-like speedup claim.

| Wire item | V8 bytes | Headroom to 4,096 B |
| --- | ---: | ---: |
| Proof body, stored in account | 54,604 | not transaction-carried |
| Sealed ASPU account, including 40-byte header | 54,644 | not transaction-carried |
| Canonical public inputs | 216 | included in instruction below |
| Instruction, tag 240 plus public inputs | 217 | not a complete transaction |
| **Complete signed verifier-only TxV1 proposal** | **444** | **3,652** |

The TxV1 size is obtained by actual `wincode` serialization of a signed
`VersionedMessage::V1`, including its signature, inline account keys, account
indices, instruction framing, and config. It has one signer, one read-only
proof account, a 1,400,000-CU config, 256 KiB heap request, 64 MiB loaded-data
limit, and zero priority fee. This follows the account-backed size convention
in [the V7 byte audit](../../docs/research/v7-byte-for-cu-audit-20260827.md).
CU execution uses the equivalent legacy diagnostic instruction plus compute
budget instructions; **TxV1 execution itself was not measured**.

## Phase breakdown and interpretation

**Unmined diagnostic path (PoW rejection disabled)**; checkpoint deltas include
logging/callback overhead. The source's phase order is preserved: terminal,
relation/final-polynomial checks, Merkle authentication, then query arithmetic.

| Phase | CU | Share |
| --- | ---: | ---: |
| Transcript and sumcheck replay | 140,757 | 14.25% |
| Terminal, excluding mask subphase | 272,768 | 27.61% |
| **Mask terminal subphase** | **13,945** | **1.41%** |
| Relation and final-polynomial consistency | 149,891 | 15.17% |
| Merkle/opening authentication | 176,047 | 17.82% |
| FRI query arithmetic | 231,316 | 23.42% |
| Account/public parsing, cleanup, return, other checkpoints | 3,090 | 0.31% |
| **Total** | **987,814** | **100%** |

Within the 286,713-CU terminal interval, the existing finer checkpoints report:

| Terminal subphase | CU |
| --- | ---: |
| Preparation | 42,503 |
| Poseidon | 76,671 |
| Semantic initial / absorption / Merkle / range / public | 5,056 / 5,128 / 215 / 17,688 / 11,320 |
| Copy patterns / routing / copy | 16,754 / 56,542 / 19,243 |
| Composition equality | 20,142 |
| Mask | 13,945 |
| Final / terminal return | 230 / 1,276 |

The cost is spread across field-heavy terminal and PCS arithmetic. The FRI
query and relation phases together cost 381,207 CU (38.59%); the whole
terminal costs 29.03%. Merkle/opening authentication is substantial at 17.82%,
but is not the dominant interval. It includes parsing and authentication, so
176,047 is **not** an isolated SHA-only number. Dividing by 16 gives about
11,003 CU per query for this opening interval and 14,457 for query arithmetic;
these are fixture averages, not a measured scaling slope. The isolated mask
subphase is only 1.41%; the terminal also includes a 76,671-CU Poseidon interval.
The transcript interval mixes hashes and field operations, so an exact global
hash-versus-field split is not available from these boundaries.

This measured q16 reference verifier fits comfortably in one verifier-only
instruction. These data do not justify a two-transaction split for this shape.
The intended q22 schedule and any complete Pool transaction still need their
own measurements before making that scope decision.

### M1 rejection witness (M2 prerequisite)

[rate512-q16-reject-1.json](rate512-q16-reject-1.json) uses the **same M1 ELF
and diagnostic tag 240** as the five acceptance runs. Exactly one byte was
flipped at proof offset 6,738, inside the first opened C1 leaf (52 → 53).
The changed M31 limb remains canonical (70,641,973). Both simulation and
execution reject with `InstructionError(2, InvalidInstructionData)`, with
identical logs and **628,047 verifier CU — unmined diagnostic path (PoW
rejection disabled)**. Replay, terminal and relation checks complete; Merkle
authentication does not. This is an authentication rejection, not malformed
field encoding or CU exhaustion. The sealed account remains unchanged.
[Driver build](m1-reject-driver-build.json) and [rejection resources](m1-rejection.json)
record the separate capped, zero-swap scopes; the existing SBF was not rebuilt.

## PoW omission: operation count and additive bound

The fixture is deliberately unmined (`UnminedZero`). Native diagnostic
verification accepts it; strict native verification returns
`BatchGrindingRejected`, as recorded in [fixture.json](fixture.json).

The full replay logically checks **six SHA-256 hashes and six 64-bit threshold
comparisons**: one batch, four folds, one final. Every hash receives three
slices of lengths **32 + 1 + 8 = 41 bytes** (`state || DOM_GRIND || nonce_le`).
Nonce absorption and all subsequent transcript work are retained.

The measured optimized binary **already executes all six hashes**. Batch and
final comparisons also remain. The four inlined fold comparisons are skipped
when `check_pow = false`. Each skipped block has six ordinary SBF instructions:
load, byte swap, negate shift count, mask shift count, shift, conditional jump.
There is no syscall in those blocks. Both schedule wrappers have equal
instruction counts; successful batch/final checks are no more expensive than
their diagnostic rejection-disabled paths.

Thus the omission is bounded by **0 additional hashes, 4 additional 64-bit
comparisons, and at most 4 × 6 = 24 CU** in this compiled replay. The conservative
accounting figure is **987,814 + 24 = 987,838 verifier CU**, still labelled
**unmined diagnostic path (PoW rejection disabled), plus a static PoW allowance**.
This is not a measured mined-proof result: mining changes nonces, challenges,
and queries, which can change other costs. It is a bound on the omitted check
logic only, not a claim that this fixture passes strict verification.

[pow-omission-audit.json](pow-omission-audit.json) contains the exact instruction
blocks, hash call sites, wrapper counts, and ELF hashes. The audit verifies
that the unstripped ELF used for disassembly and the measured ELF have identical
`.text` sections. Reproduce with `scripts/v8_state_only_pow_audit.py`.

## Measurement and build evidence

- [Run 1](rate512-q16-run-1.json), [run 2](rate512-q16-run-2.json),
  [run 3](rate512-q16-run-3.json), [run 4](rate512-q16-run-4.json),
  [run 5](rate512-q16-run-5.json): separate simulation/execution status, logs,
  meters, proof/public/ELF hashes, and phase deltas; all accepted and identical.
- [summary.json](summary.json) is regenerated and cross-checked by
  `scripts/v8_state_only_cu_summarize.py`.
- Runtime: **LiteSVM 0.16.0, Agave runtime 4.2.1**, pinned by the separate tool's
  committed `Cargo.lock`. SBF builder: **Agave CLI/cargo-build-sbf 3.1.13,
  platform-tools v1.52, SBF rustc 1.89.0**. Host rustc/cargo: **1.94.1**.
  These are distinct toolchain and execution-runtime versions.
- Host: **`nuc`, `dombarker@100.108.41.90`**, Intel Core Ultra 7 155H, approximately
  62 GiB physical RAM, Linux `6.8.0-142-generic`.
- Builds, fixture generation, and checks each used a separate scope with
  **MemoryHigh=8 GiB, MemoryMax=12 GiB, MemorySwapMax=0**. Measurement used
  **4 / 6 GiB, swap max 0**. Maximum concurrent reservation by this task was
  24 GiB. Every completed task scope reports zero swap; the host's pre-existing
  system swap usage is separately recorded and is not attributed to this task.

| Job | Exit | Wall seconds | Sampled aggregate RSS MiB | Cgroup memory peak MiB |
| --- | ---: | ---: | ---: | ---: |
| Final SBF build | 0 | 68.549 | 271.00 | 146.56 |
| Release native driver build | 0 | 113.102 | 962.72 | 1,573.34 |
| Fixture generation + host acceptance checks | 0 | 13.511 | 173.98 | 170.97 |
| Five paired LiteSVM runs | 0 | 0.501 | 12.50 | 32.96 |
| Production feature-off rejection test | 0 | 67.562 | 886.23 | 1,022.96 |
| Feature-on production-dispatch rejection test | 0 | 28.527 | 984.79 | 720.55 |
| Release `xtask` check | 0 | 37.531 | 771.48 | 890.54 |

Wall time includes Cargo lock waits and the resource monitor's 0.5-second
polling. The final SBF build waited for the host test's shared Cargo target
lock; no repeated full regression was run. Sampled process RSS counts shared
resident mappings per process and can exceed cgroup memory accounting; the
short measurement also finishes between samples. Both metrics and child
`ru_maxrss` are retained, rather than treating sampled RSS as an exact peak.

The initial SBF build failed because the program's existing unconditional
V7 module required the existing `pool-v1-kernel` dependency feature. Only the
new probe's feature forwarding was corrected. Initial host resolution failed
because LiteSVM requires `wincode` 0.5.5; that exact version is now pinned.
These failures and their replacements are preserved in resource JSON and
[build-log-excerpts.json](build-log-excerpts.json). No memory-pressure retry
or cap increase occurred.

[environment.json](environment.json) records tool versions, host details,
artifact sizes/hashes and retained paths. [source-manifest.json](source-manifest.json)
pins 339 input files, all checked against the build host. Early build/fixture
records carry the base label `dd621ba62`: those native input files were the
uncommitted sources subsequently committed at `2940f8a73`. Final SBF and run
records name that full commit. The final input manifest confirms their bytes.

The sealed proof account is preloaded with ASPU magic, exact length, and zero
upload-authority bytes; it is program-owned and passed read-only. Its data is
unchanged after every execution. Public inputs use the canonical 216-byte
atomic statement encoding. The feature is default-off; tag 240 has its own
entrypoint and cannot coexist with a production entrypoint. Both focused
release tests prove that production dispatch rejects it with zero accounts.

The raw diagnostic harness meter is 988,170 CU (verifier plus 300 CU for budget
instructions and 56 CU of heap charge). This is recorded to reconcile the
simulation/execution meters; **it is not a Pool transaction-level CU result**.
No Pool CPI, receipt, settlement, upload, or live-network transaction was
measured. Marker overhead is included; there is no uninstrumented-total claim.

Proof/public binaries, SBF/native binaries, raw logs, and generated program
key remain under `/home/dombarker/project-offloads/aspis-v8-state-only-cu-20261009/`.
The LiteSVM-only payer key is retained with mode 0600. No key cleanup or network
fund movement occurred. Only sources, scripts, lockfiles, and JSON/Markdown
evidence are committed here; no binaries or proof blobs are committed.

## Reproduction

Run on the Linux build host. Inspect other active reservations first and keep
combined caps within the host's safe working limit. Each `scope` invocation
below creates its own capped job. Use a fresh evidence directory and retain
any generated keys. Heavy time is expected in compilation and then fixture
generation; the measured step itself is release LiteSVM execution.

```bash
export PATH="$HOME/.cargo/bin:$HOME/.local/share/solana/install/releases/3.1.13/solana-release/bin:$PATH"
export ASPIS_SOURCE_REVISION="$(git rev-parse HEAD)"
export CARGO_BUILD_JOBS=2
task_output=/absolute/new/m1-evidence
mkdir -p "$task_output"
scope() {
  label=$1
  shift
  systemd-run --user --scope --unit="aspis-v8-m1-$label-$$" \
    -p MemoryHigh=8G -p MemoryMax=12G -p MemorySwapMax=0 \
    python3 scripts/v8_state_only_cu_record.py "$task_output/$label" "$@"
}
scope sbf cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml \
  --sbf-out-dir "$task_output/sbf" --no-default-features \
  --features v8-state-only-cu-probe -- --locked -j 2
scope host cargo build --release --locked \
  --manifest-path tools/v8-state-only-cu-probe/Cargo.toml -j 2
scope fixture tools/v8-state-only-cu-probe/target/release/aspis-v8-state-only-cu-probe \
  fixture "$task_output/fixtures"
scope measure tools/v8-state-only-cu-probe/target/release/aspis-v8-state-only-cu-probe \
  measure "$task_output/sbf/aspis_verifier.so" "$task_output/fixtures" "$task_output/runs"
python3 scripts/v8_state_only_cu_summarize.py "$task_output/runs"
```

The requested `xtask` entry is also available, inside the same capped scope:
`cargo run --release --locked -p aspis-xtask -- v8-state-only-cu-probe fixture DIR`
or `... v8-state-only-cu-probe measure ELF FIXTURE_DIR RESULTS_DIR`. It delegates
to the same locked release driver. The direct driver invocation above avoids
building unrelated xtask dependencies for a measurement-only rerun.
