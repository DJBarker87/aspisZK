# M1: state-only reference verifier CU

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
