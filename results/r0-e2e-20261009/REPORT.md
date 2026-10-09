# R-E: end-to-end R0, 2026-10-09

**Native end-to-end integration passes. This implementation does not fit one
Solana transaction as shipped: every SBF run crashes with a stack access
violation before completing the semantic phase. Full verifier CU, downstream
phase CU, and headroom to 1.3M/1.4M are unavailable. The consumed CU of a crashed
invocation is not an accepted-proof measurement.**

Base: `e5d4e1a3d`; work began after R-G landed on `v8-reference` at
`9789ea8b6`. Integration/probe source: `928f8855b`. Final prover continuation
and direct prover-RSS sampling: `1ef8cc85b`. Branch:
`codex/r0-e2e-re-20261009`.

## Results beside M1

| Measurement | M1 historical | R0 transfer | R0 withdrawal |
| --- | ---: | ---: | ---: |
| Proof bytes | 54,604 | 95,712 | 95,712 |
| Prover wall seconds | 13.089 fixture build | 5.072 | 5.180 |
| Prover-process peak RSS MiB | unavailable on this exact scope | 193.34 | 193.30 |
| Strict native accepted | no: diagnostic PoW bypass | yes | yes |
| Native verifier seconds | not recorded here | 0.06097 | 0.06250 |
| Paired simulation/execution runs | 5 successful | 5 identical failures | 5 identical failures |
| Completed verifier CU | 987,814 diagnostic | unavailable | unavailable |
| Headroom to 1,300,000 CU | 312,186 | unavailable | unavailable |
| Headroom to 1,400,000 CU | 412,186 | unavailable | unavailable |
| Failed invocation consumed CU | — | 17,645 | 17,593 |
| Raw harness CU | 988,170 | 18,001 | 17,949 |
| Proposed signed TxV1 bytes | 444 | 261 | 261 |
| One verifier transaction works as implemented | yes, diagnostic scope | **no** | **no** |

R0 peak RSS is Linux `VmHWM` read immediately after preparation and proving,
before native verification. Prover wall time covers `r0_prove` (commitments,
semantic sumcheck and opening), excluding fixture preparation. These are
single fixture-generation timings, not a statistical benchmark. The final
fixtures reproduce both earlier measured proof/public hashes exactly.
See [transfer](final-fixtures/transfer.fixture.json),
[withdrawal](final-fixtures/withdrawal.fixture.json), and [summary](summary.json).

M1 is a different protocol: atomic Rate512/q16, four-fold QM31 PCS,
PoW rejection disabled. R0 uses PF semantics, P1+D13, 22 distinct fibres and
strict acceptance with no disabled checks or PoW schedule. M1's 24-CU static
PoW allowance is historical, not applied to R0. Its phase data and full
scope are in [the original report](../v8-state-only-cu-20261009/README.md)
and [summary](../v8-state-only-cu-20261009/summary.json). Neither result
includes a Pool CPI, settlement, receipt, proof upload, or network execution.
R0 uses an additional read-only public-context account; transaction sizes
therefore do not compare identical transports. Signed TxV1 sizes are
serialized proposals; the LiteSVM CU runs execute the legacy envelope.

## Phase split and runtime failure

| Phase | M1 corresponding interval, CU | R0 transfer / withdrawal |
| --- | ---: | --- |
| Semantic transcript/sumcheck + terminal | 140,757 + 286,713 | unavailable: phase did not finish |
| Chord/claims | 149,891 relation/final-polynomial interval, different algorithm | not reached |
| V1 per fibre | 231,316 aggregate FRI-query arithmetic; 14,457.25 per query average | all 22 unmeasured |
| V2 | no separately measured counterpart | not reached |
| Merkle | 176,047 | not reached |
| Other M1 work | 3,090 | not comparable |

The R0 observer marks semantic completion, chord/claim preparation,
authentication and V1 **for each of 22 fibres**, and V2 including basis
construction. Markers are passive; all checks execute on the same
`r0_verify` path. Authentication precedes V1 for each fibre; deltas separate
their costs without moving checks. Marker overhead is included.

Only `begin` and `parsed` occur in these runs. Their 240-CU delta covers the
fixed-length split and marker overhead, not full canonical parsing. The
next phase crashes. `summary.json` explicitly records null for incomplete
phases, all 22 V1 entries, all 22 Merkle entries, and both headrooms.

All ten simulations and executions agree on status, meter and every log;
both accounts remain unchanged. Raw run JSON retains `verifier_cu` as the
runtime's **consumed-before-failure** number with `verifier_completed=false`;
the summary exposes it only as `failed_invocation_consumed_cu`, with
`completed_verifier_cu=null`. Example:

```text
InstructionError(2, ProgramFailedToComplete)
Access violation in stack frame 5 at address 0x200005f48 of size 432
```

[Transfer runs 1–5](transfer-run-1.json), [2](transfer-run-2.json),
[3](transfer-run-3.json), [4](transfer-run-4.json), [5](transfer-run-5.json).
[Withdrawal runs 1–5](withdrawal-run-1.json), [2](withdrawal-run-2.json),
[3](withdrawal-run-3.json), [4](withdrawal-run-4.json), [5](withdrawal-run-5.json).

The compiler returns exit zero while reporting invalid stack layouts. This
is **not a successful SBF validation**. Relevant estimated frames include:
`r0_verify` 49,536 bytes; `semantic_handoff` 15,872;
`verify_semantics` 15,104; opening `prepare` 12,928;
`check_v1` 75,904; `check_v2` 106,816. The frame limit is 4,096 bytes.
[All compiler diagnostics](sbf-stack-diagnostics.json) preserve exact
messages; some additional diagnostics are unused prover instantiations,
so no claim is made that every reported function survives linking.

Independently, `NaturalBasis::new(Initial)` allocates two 512×512 M31
matrices: **2,097,152 bytes**, before its work vectors. This exceeds the
probe's **262,144-byte heap**. The crash occurs earlier, so that is a source
layout obstruction, not an observed allocation-failure result. A usable
SBF path needs bounded-stack/heap representations throughout the semantic
and opening consumers and a different storage/evaluation strategy for the
basis. No conclusion about the eventual optimized CU cost or a two-
transaction split follows from this crash.

## API, handoff and wire

- `aspis_prover::r0::r0_prove`: row-indexed lanes, compiled PF trace, caller
  mask material, hash backend; returns one P1 proof for either public variant.
- `aspis_statement::r0::r0_verify`: public input, bytes, SHA-256 backend,
  optional diagnostic callback; runs semantic and authenticated opening
  acceptance. There is no caller-supplied acceptance flag in this entrypoint.
- `semantic_handoff`: successful R-F verification supplies the state before
  row 25, C1/C2 roots, all 25 K challenges and all 87 E claims. R-D derives
  its three points; the hook checks them against R-F's three MSB/LSB-adjusted
  statement points. Both layers must replay identical circle points.
- C1 commits lanes 0–25 and D at lane 28 before lambda/chi. The actual helper
  callback builds C2 lanes H1/G at 26/27 afterward. R-G receives row-indexed
  inputs and transports them internally; weights use the fixed D13 order.
- `build_pair_forest_transported` supplies D13's endpoint before z1. It
  prevents an unused raw-row z1/equality abort. The existing standalone
  semantic diagnostic builder/KATs retain their original behavior. The
  prover checks the two row-26 records agree before emitting them once.

Wire = C1 root + semantic records 0–25 + R-D records beginning at row 26.
The borrowed semantic prefix is 12,903 bytes; the opening view starts at
11,970; its 83,742 bytes overlap the 933-byte row-26 record. Total =
**95,712 bytes**. No extra header, nonce or challenge is introduced. The
row-29 unit is implicit in the compact wire and explicitly absorbed by R-D;
row 30 reconstructs c4 and absorbs seven coefficients. Row-26 Y0 remains
separate from row-27's endpoint values, as P1 requires; the verifier adds
no equality restriction between those two algebraic messages. Strict
parsers enforce fixed lengths/tags, canonical limbs, narrow F/K openings,
22 paths, and no trailing bytes.

Mask inputs and the deterministic fixtures do not certify any entropy or
privacy distribution. No Rust-to-Lean refinement or formal release gate is
closed by these executable tests.

## Fixtures and rejection evidence

[Transfer proof](transfer.proof.bin) / [public context](transfer.public.bin)
and [withdrawal proof](withdrawal.proof.bin) /
[public context](withdrawal.public.bin) are genuine end-to-end PF proofs,
not synthetic accepted semantic boundaries. Their 1,880-byte public-context
files use the existing ASF8 codec; the transcript still hashes only P1's
canonical `R0P.Public` bytes. The final prover reproduced these exact files.

[The native test](../../crates/aspis-prover/tests/r0_e2e.rs) passed both
round-trips and **1,894 recorded rejection cases** in
[corruption-cases.json](corruption-cases.json): every semantic row's framing
(including empty rows), every nonempty row message, canonicality, all ten
sumcheck boundary checks, terminal claim failures, every one of 87 claims,
all opening record fields (including all 256 F coordinates), C1 root,
C2 root, authentication headers, both trees and all six levels for every
sampled fibre, every slot/lane on the first fibre and a leaf on every fibre,
and changed public input. Fixed-challenge tests separately force V1 and all
six transmitted polynomial coefficient failures at V2 while retaining an
honest control for the other predicate. Existing R-G KAT/sampler/chord
validation is retained; it was not rerun unchanged.

Feature-off and feature-on tests both confirm production dispatch rejects
tag 241 before account access. The new default-off `r0-cu-probe` entrypoint
is compile-time incompatible with production and other diagnostic
entrypoints. The probe checks owner, read-only status, sealed ASPU proof
bounds, and canonical ASF8 context. No production dispatch is changed.
The original M1 executable/default command remains available; its locked
LiteSVM harness is reused by the separate `r0-e2e-cu-probe` binary.

## Resources and reproducibility

All build-host jobs use their own systemd scopes, **MemoryHigh=4 GiB,
MemoryMax=6 GiB, MemorySwapMax=0**, with two compiler jobs and optimized
arithmetic. Heavy time is compilation followed by semantic sumcheck/proof
generation; the opening quotient is the existing sparse solve. The source
hash audit and active reservation snapshot run before the final jobs.
Maximum recorded aggregate reservation including other work was 16 GiB,
below the 50 GiB working limit. Caches were reused. No memory-pressure
retry, cap increase, full Lean replay, or unchanged SBF rerun occurred.

| Job | Exit | Wall s | Sampled aggregate RSS MiB | Cgroup peak MiB | Swap bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| [preflight](preflight.json) | 101 | 6.505 | 690.79 | 507.53 | 0 |
| [driver-build](driver-build.json) | 0 | 43.552 | 1050.46 | 845.52 | 0 |
| [fixture-transfer](fixture-transfer.json) | 0 | 6.508 | 196.84 | 197.58 | 0 |
| [fixture-withdrawal](fixture-withdrawal.json) | 0 | 6.007 | 196.86 | 197.71 | 0 |
| [e2e-tests](e2e-tests.json) | 0 | 55.564 | 1027.64 | 805.95 | 0 |
| [sbf-build](sbf-build.json) | 0 | 28.037 | 1181.12 | 933.48 | 0 |
| [measure-transfer](measure-transfer.json) | 0 | 0.501 | 12.89 | 22.52 | 0 |
| [measure-withdrawal](measure-withdrawal.json) | 0 | 0.501 | 12.85 | 22.05 | 0 |
| [feature-off](feature-off.json) | 0 | 76.582 | 901.77 | 1023.31 | 0 |
| [feature-on](feature-on.json) | 0 | 31.031 | 985.68 | 720.98 | 0 |
| [final-driver-build](final-driver-build.json) | 0 | 15.514 | 580.63 | 435.96 | 0 |
| [final-fixture-transfer](final-fixture-transfer.json) | 0 | 5.505 | 196.82 | 197.63 | 0 |
| [final-fixture-withdrawal](final-fixture-withdrawal.json) | 0 | 5.505 | 196.87 | 198.22 | 0 |
| [semantic-regression](semantic-regression.json) | 0 | 18.015 | 561.07 | 424.28 | 0 |
| [no-std](no-std.json) | 0 | 0.501 | 12.60 | 53.85 | 0 |

The initial preflight failed on a missing `CodeField` import; the corrected
source built successfully. The SBF command's zero exit is recorded alongside
its stack diagnostics and runtime failure. Resource wall time includes
compilation and monitoring; short measurements can complete between the
0.5-second RSS samples. Child peak RSS and cgroup peaks are retained.
`#print axioms`: not applicable, Rust-only work.

[Environment](environment.json) pins Linux/CPU/tool versions and ELF hashes.
Runtime: LiteSVM 0.16.0 / Agave 4.2.1. Builder: Agave 3.1.13,
platform-tools 1.52 / SBF rustc 1.89.0. Host Rust 1.94.1.
[Measured source manifest](measured-source-manifest.json) names `928f8855b`;
[final source manifest](source-manifest.json) names `1ef8cc85b`. The summary
verifies all core, statement, verifier-program and root Cargo inputs are
unchanged across the final prover-only correction. Since both final fixtures
are byte-identical, the ten existing SBF runs remain evidence for the final
verifier. The native driver was rebuilt only for the changed prover/RSS
sampling, followed by both fixtures, the four affected semantic tests and a
no_std check. The unchanged 1,894-case verifier suite was not repeated.

Build-host workspace:
`/home/dombarker/project-offloads/aspis-r0-e2e-20261009`.
The program and LiteSVM payer keys remain there with mode 0600. No key was
deleted and no network transaction was sent. ELF/native binaries remain on
the host; fixtures, source manifests, logs and JSON/Markdown evidence are
retained here.

Run from a matching source checkout on the Linux host. The launcher audits
`source-manifest.json` and reserves a capped scope. `R0_TARGET_DIR` can select
an existing compatible compiled cache.

```text
python3 scripts/r0_e2e_run.py driver-new cargo build --release --locked --offline --manifest-path tools/v8-state-only-cu-probe/Cargo.toml --bin r0-e2e-cu-probe
python3 scripts/r0_e2e_run.py transfer-new /absolute/target/release/r0-e2e-cu-probe fixture results/r0-e2e-20261009 transfer
python3 scripts/r0_e2e_run.py withdrawal-new /absolute/target/release/r0-e2e-cu-probe fixture results/r0-e2e-20261009 withdrawal
python3 scripts/r0_e2e_run.py teeth-new cargo test --release --locked --offline -p aspis-prover --features r0,insecure-spend-fixture --test r0_e2e -- --include-ignored --nocapture --test-threads=1
python3 scripts/r0_e2e_run.py sbf-new cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --sbf-out-dir /absolute/new/sbf --no-default-features --features r0-cu-probe -- --locked -j 2
python3 scripts/r0_e2e_run.py measure-new /absolute/target/release/r0-e2e-cu-probe measure /absolute/new/sbf/aspis_verifier.so results/r0-e2e-20261009 /absolute/new/runs transfer
python3 scripts/r0_e2e_summarize.py results/r0-e2e-20261009
```

Use fresh evidence labels/outputs for new measurements and preserve prior
runs. A new full CU claim requires correcting the live SBF memory layout,
then rerunning the same strict acceptance and phase instrumentation. The
current blocker is recorded rather than bypassed.
