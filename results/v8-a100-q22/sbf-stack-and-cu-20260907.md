# V8 two-point DEEP SBF stack and CU evidence

Date: 2026-09-07

Research branch: `research/v8-sbf-stack-refactor-current`

Base revision: `ec74d86f114b53715fa3691aac87763fe72e4e26`

Implementation revisions, in order:

- `9de33d2e` — add stack-safe heap-batched and pointwise quotient candidates
- `9d76723a` — stream the four gamma dots without a 4-by-29 QM31 matrix
- `4a8f8641` — add a mutually exclusive, test-only LiteSVM probe
- `f8450608` — derive private challenges through `V8A100OodPrefix::challenges`
- `eb652911` — isolate transcript derivation and probe runner stack frames
- `226e8f36` — separate canonical parsing from quotient-kernel CU probes

No challenge fields were made public. The probe obtains its challenges only by
calling the production transcript-prefix API. The feature is default-off and
mutually exclusive with every production and release-probe entrypoint. No RPC,
validator, signing service, deployed program, or live state was used or
modified.

## Result and boundary

Both materially different quotient kernels compile to reachable SBF frames
below the 4,096-byte VM limit and run successfully in LiteSVM under the
1.4-million-CU instruction limit:

| Probe | Largest kernel frame | Total transaction CU | Program CU | Kernel-region CU |
|---|---:|---:|---:|---:|
| heap-batched, one inversion | 2,176 | 807,012 | 806,862 | 750,111 |
| pointwise, 88 inversions | 2,112 | 791,539 | 791,389 | 734,638 |
| canonical parse only | 192 | 634,879 | 634,729 | 633,942 |

`Kernel-region CU` is the exact difference between the two runtime remaining-CU
samples surrounding the named region. It includes the quotient function and
the caller's checksum over all 88 outputs, but excludes transcript setup.

The pointwise result is unexpectedly 15,473 CU cheaper than the heap-batched
probe on this all-zero syntactically canonical fixture. It is not evidence that
88 general inversions are cheaper: these field inversions see a highly special
input distribution. The host equality test, rather than the CU fixture,
establishes semantic agreement with the slow reference implementation.

This is an isolated verifier-kernel measurement, not a complete V8 verifier or
Pool transaction. It deliberately performs no Merkle authentication, folding,
terminal checks, settlement, or CPI. The body is 39,934 bytes and uses the exact
maximum-frontier q22 schedule, but contains canonical zero field encodings and
is not an accepting production proof. No complete V8 same-page or rollover CU
measurement exists because the repository does not yet have a complete V8
verifier/Pool integration or an honest V8 proof fixture.

The three independent probe totals cannot be added as a prediction for a
complete verifier: the quotient modes use deferred canonicality and include
their own entry/transcript work, while the parse mode includes a separate
entry. An earlier combined full-canonical-parse plus heap-kernel experiment did
reach the kernel with 723,486 CU remaining and then exhausted the 1.4M limit.
That failure established that the straightforward combined shape is not
viable; it did not measure a complete verifier and was not rerun after phase
isolation.

## Stack evidence

The unmodified source initially compiled these two V8 functions with unsafe SBF
frames even though the V7 linker removed them:

| Function | Initial frame | Initial maximum offset |
|---|---:|---:|
| return-by-value slow reference | 11,904 | 11,800 |
| return-by-value optimized implementation | 18,880 | 18,048 |

Moving only the q22-wide arrays to the heap reduced both experimental paths to
7,168-byte frames, still above the SBF limit. The decisive refactor also:

- makes the caller own the 88-value output;
- generates the four fibre points one query at a time;
- streams C1 lifts and native C2 values directly into four gamma accumulators;
- moves batch-inversion prefixes and q22-wide scratch to heap storage; and
- excludes return-by-value reference functions from the Solana target.

Exact final `.stack_sizes` records from the pinned v1.48 LLVM tools are:

| Function | Frame bytes |
|---|---:|
| `validate_wire_component_vectors` | 1,920 |
| `decode_v8_query_gamma_dots_streaming` | 1,472 |
| `batch_inverse_heap_in_place` | 256 |
| `v8_deep_quotients_heap_batched_in_place` | 2,176 |
| `v8_deep_quotients_pointwise_in_place` | 2,112 |
| `derive_probe_challenges` | 3,968 |
| `run_deep_probe` | 3,136 |
| `run_canonical_parse_probe` | 192 |
| entrypoint | 128 |

No function reachable from the test-only probe exceeds 4,096 bytes. One
production-facing helper that the probe intentionally does not call,
`derive_v8_a100_ood_prefix_from_wire`, still compiles with a 4,736-byte frame
(`0x1280`). This is the exact remaining stack blocker for a future production
V8 entrypoint that calls the convenience helper directly. The stack-safe probe
instead separates wire parsing from `derive_v8_a100_ood_prefix`, whose frame is
768 bytes, without changing transcript semantics.

## SBF artifact and resource envelope

Linux host/toolchain:

- host: `nuc.local`, Linux x86_64, task-owned disposable source copy
- `solana-cargo-build-sbf 2.3.0`
- platform tools v1.48 / Rust 1.84.1
- Agave runtime 4.2.1 through LiteSVM 0.16.0
- SBF artifact: 190,432 bytes
- artifact SHA-256: `b0ad304444c678036437d86205806b21b8b4deff48189243429ae7fd66ac8db7`

The SBF build ran under `MemoryHigh=5G`, `MemoryMax=7G`,
`MemorySwapMax=0`; it exited 0 in 27.36 seconds with maximum RSS 553,320 KiB
and zero swaps. The final LiteSVM run used the same bounds; `/usr/bin/time`
reported 0.69 seconds, maximum RSS 267,276 KiB, and zero swaps. The cgroup
reported zero swap; its post-exit `Memory peak` display is not used because it
does not retain the child peak reliably, while `/usr/bin/time` does.

Machine-readable LiteSVM output is in
`sbf-deep-cu-current-20260907.json` (SHA-256
`51988cd4200aa8ccf834bc2823add688150ea7a490c0d451265309998b5db428`).

## V7 proof-body baseline discrepancy

The source arithmetic value 30,504 bytes applies to the compact packed fixed
grammar. The retained LiteSVM fixtures exercise feature
`v7-pair-forest-one-tx-candidate`, which enables
`v7-pair-forest-fixed-canonical-exact-once-audit`. That feature stores 641
fixed QM31 values as 16 bytes each: 10,256 bytes, not the 9,936-byte compact
packed field block. The exact 320-byte increase explains the fixture sizes:

- body without frontiers: 20,268 bytes;
- same-page fixture: `20,268 + 2 * 203 * 26 = 30,824` bytes;
- rollover fixture: `20,268 + 2 * 202 * 26 = 30,772` bytes.

The harness's `proof_body_bytes` excludes the 688-byte after-state. Therefore
the discrepancy is a feature-selected fixed-field grammar difference, not a
proof header, pair-forest framing, or after-state accounting error.

## Reproduction

Focused host equivalence:

```text
cargo test -p aspis-core no_new_tree_wire_path_matches_slow_reference --locked
```

Feature wiring without an entrypoint:

```text
cargo check -p aspis-verifier --no-default-features \
  --features v8-deep-cu-probe,no-entrypoint --locked
```

SBF build (run on Linux in a bounded scope):

```text
ssh dombarker@nuc.local systemd-run --user --wait --collect --pipe \
  --unit=aspis-v8-sbf-current-eb652911-r1 \
  -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 -p OOMPolicy=stop \
  /usr/bin/time -v env NO_DNA=1 RUSTC_BOOTSTRAP=1 \
  RUSTFLAGS=-Zemit-stack-sizes \
  PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/releases/2.3.0/solana-release/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
  /home/dombarker/.local/share/solana/install/releases/2.3.0/solana-release/bin/cargo-build-sbf \
  --manifest-path /home/dombarker/project-offloads/aspis-v8-sbf-current-eb652911-20260907-r1/source/programs/aspis-verifier/Cargo.toml \
  --no-default-features --features v8-deep-cu-probe --arch v0 --offline \
  --skip-tools-install --tools-version v1.48 \
  --sbf-sdk /home/dombarker/.local/share/solana/install/releases/2.3.0/solana-release/bin/platform-tools-sdk/sbf \
  --sbf-out-dir /home/dombarker/project-offloads/aspis-v8-sbf-current-eb652911-20260907-r1/sbf-probe \
  -- --locked
```

Stack records:

```text
llvm-readobj --stack-sizes \
  target/sbpf-solana-solana/release/deps/libaspis_core-*.rlib
llvm-readobj --stack-sizes \
  target/sbpf-solana-solana/release/deps/libaspis_verifier.rlib
```

LiteSVM probe (also run in the same bounded scope):

```text
ssh dombarker@nuc.local systemd-run --user --wait --collect --pipe \
  --unit=aspis-v8-deep-litesvm-eb652911-r1 \
  -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 -p OOMPolicy=stop \
  /usr/bin/time -v env \
  CARGO_TARGET_DIR=/home/dombarker/project-offloads/aspis-v8-sbf-baseline-e8627859-20260907-r1/source-complete/results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/target \
  PATH=/home/dombarker/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
  /home/dombarker/.cargo/bin/cargo run --release --locked --offline \
  --manifest-path /home/dombarker/project-offloads/aspis-v8-sbf-current-eb652911-20260907-r1/source/results/v8-a100-q22/sbf-deep-probe-harness/Cargo.toml -- \
  /home/dombarker/project-offloads/aspis-v8-sbf-current-eb652911-20260907-r1/sbf-probe/aspis_verifier.so \
  /home/dombarker/project-offloads/aspis-v8-sbf-current-eb652911-20260907-r1/deep-cu.json
```

## Failure classification and next action

- Original 11,904/18,880-byte frames: resource-layout problem. Returning and
  materializing q22-wide arrays overlapped in the SBF frame.
- Heap-only 7,168-byte attempt: incomplete resolution of the same problem; the
  4-by-29 decoded component matrix remained live.
- First combined 1.4M-CU exhaustion: resource exhaustion in a deliberately
  isolated kernel probe, caused by combining a 39,934-byte canonical scan with
  the unsplit DEEP path.
- Remaining 4,736-byte convenience helper: source/API integration problem,
  reduced to one exact function. It has not affected the current probe because
  it is unreachable there.

The most valuable next SBF task is to refactor
`derive_v8_a100_ood_prefix_from_wire` into parser-owned scratch or a
borrowed/streaming prefix API, then build a complete test-only V8 verifier
entrypoint. Only that source path can support honest verifier-only, same-page,
and rollover measurements; the present kernel CU must not be advertised as a
transaction feasibility result.
