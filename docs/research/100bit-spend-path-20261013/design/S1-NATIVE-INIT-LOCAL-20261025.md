# S1 native Claims initialization: isolated compiler failures and allocator limit

Status: **S1 OPEN; no enclosing initializedness premise removed.** S6 is
unchanged. This is a source-only `focused-extractor-proof-packet-v1`
diagnostic packet, not a Lean proof or a successful native initialization check.

The source freeze remains `25866ec331cc7ce27dd9956609c11d32fa8fa58a`.
No production source, protocol, parameters, SBF artifact, or other owner's
track was changed. The complete frozen `r1_semantic.rs` and `heap.rs` are
retained beside the diagnostics. The one-row `native_step` still contains
the frozen claims loop's exact pointer cast/add/write and `decode_k(p*29)?`.
The checked integrity gate compares that fragment and the old/new harness
function text; this is a source check, not whole-function semantic equivalence.

## New evidence that changes the next action

The Kani 0.67 initialization-check crash is reproducible locally on Apple
Silicon with the same Rust compiler commit as the Linux attempt. The official
release binary statically disables TRACE; setting `KANI_LOG=...=trace` cannot
reveal the current transformation function. The compiler emits that limitation
explicitly in v2. A full backtrace in v3 identifies the initialization visitor,
but does not identify the offending type.

Two small controls then isolate independent failures:

* v14: `kani::any::<[[u32;4];29]>()` alone reproduces the original
  `ty_layout.rs:190` Primitive/Scalar ICE. v17's independent scalar-by-scalar
  symbolic generation of the same full word array compiles with initialization
  checks. No canonicality restriction is imposed on those symbolic words.
* v25: a bounded dynamic slice `&frame[..n]`, `n < 3718` on 3717 bytes,
  reproduces the formatting function-pointer limitation. The full harness
  instead uses `get(..n)` and an assertion failure on `None`; it does not
  assume the slice succeeds or restrict the symbolic length domain.

The full one-row harness compiles in v26 after those proof-harness changes
and replacing `assert_eq!` formatting with the same operand equality under
`assert!`. Original frozen native function bytes and the decoder stub remain
available for comparison. These changes have **no adoption/re-pin requirement
for production**, but the modified harness needs independent scope review
before a future successful result could replace the old harness evidence.

Actual verification does not establish initializedness:

* v27: 1 of 706 checks fails on Kani's unsupported raw-pointer/union
  interaction in `Box::new(MaybeUninit::uninit())`. That allocation was part of
  the historical one-row harness, not the frozen implementation's allocation.
* v28 replaces that harness allocation with the actual frozen
  `aspis_core::r0::heap::uninit::<Claims>()`, retaining and checking its
  allocation-error branch. Compilation succeeds.
* v30 verification fails because Kani cannot determine the initialization
  layout for niche-encoded `alloc::collections::TryReserveErrorKind`, reached
  through the actual `try_reserve_exact` allocator path. The run reports zero
  cover properties satisfied. Neither nonfailing checks nor code generation
  are promoted to proof of the complete harness.

There is **no opaque allocator replacement**, disabled initialization check,
assumed allocation success, compiler patch, new source candidate, or successful
initialization proof in this packet. The next native deliverable needs a
sound way through that real allocator boundary, including its rejection path.
Another unchanged retry or larger memory limit does not address this failure.
The complete loop, error/drop behavior, and full enclosing caller refinement
remain obligations even after an eventual successful row check.

## Execution, pins, and resource scope

This is a NEW macOS/aarch64 diagnostic, not a replay of Linux or SBF behavior.
Official asset `kani-0.67.0-aarch64-apple-darwin.tar.gz`, 104168339 bytes,
SHA256 `7fd0b71130aa37bd1e346eba675aad09e9b66e4b383f707fc657330ceb29eeec`,
matches its release metadata. Its private installation and generated binaries
remain under `/private/tmp/s126-kani-local-diagnostic-20261025-v1`; none are
committed. The existing Mac nightly reports
`rustc 1.93.0-nightly (53732d5e0 2025-11-20)`.

All 88 core input files and five minimal-crate source/lock files match the
retained Linux manifest. Exact Git-origin hashes, proof-only source variants,
per-attempt commands/environment/features, package/tool hashes, output hashes,
and source/tool pre/post checks are retained. The tool pin set covers the
Kani package, Rust/Cargo executables, and host top-level dylibs. It is not a
complete pre/post census of the host compiler's sysroot rlibs, macOS system
frameworks, or all runtime imports; no coherent formal release/tool-closure
claim is made from these diagnostics. v1-v7 lack contemporaneous driver/source
snapshots; their existing input pins/raw logs are retained without invented
historical snapshots. v8 onward includes driver and variant source snapshots.

Each local job used one compiler slot, the atomic shared mkdir lock, a
process-group watchdog at 2 GiB aggregate RSS, 64 processes and 180 seconds,
and one Cargo job. These are focused small local jobs, not a Linux cgroup
claim or proof of a hard no-swap OS policy. All recorded process swaps were
zero and no watchdog fired. The old default-check predecessor measured
1,467,384 KiB RSS; the new runs stayed far below that. No NUC/SSH operation,
global installation, container launch, or other owner's lock removal occurred.
v29 was rejected before launch by an existing shared lock; v30 started only
after it disappeared. `#print axioms`: N/A, no Lean target or new theorem.

| Attempt | Actual result | Exit | Wall s | time RSS bytes | Observed aggregate RSS bytes | Swaps |
|---|---|---:|---:|---:|---:|---:|
| v14 | array sampler layout ICE | 1 | 0.228339 | 180240384 | 1458176 | 0 |
| v17 | scalar sampler compile only | 0 | 0.457399 | 145293312 | 22069248 | 0 |
| v25 | bounded slice formatting ICE | 1 | 0.453036 | 191135744 | 221331456 | 0 |
| v26 | full revised harness compile only | 0 | 1.569835 | 309379072 | 248332288 | 0 |
| v27 | unsupported union verification failure | 1 | 3.173462 | 153419776 | 168607744 | 0 |
| v28 | real allocator harness compile only | 0 | 2.952378 | 405864448 | 432701440 | 0 |
| v30 | real allocator niche-layout verification failure | 1 | 2.703731 | 147079168 | 173359104 | 0 |

Very short jobs can finish between watchdog samples, so the sampled aggregate
maximum is not a complete historical peak measurement; both metrics are
reported separately. Earlier setup failures (missing lexical directory and
tool PATH), assertion-formatting controls, and the collector's initial
duplicate-key failure are retained and excluded from proof claims.

Integrity validation, with no compiler replay:

```
python3 tools/s1-init-local-20261025/check.py
```

It passes 338 pinned source/evidence files. Evidence:
`evidence/s126-current-caller-20261021/s1-init-local-20261025/manifest.json`,
`results.json`, and sibling `s1-init-local-compile-v1` through `v30` attempts.
This does not change the retained S1 accepted-caller trace/challenge-range
results, the S6 decoded-statement reuse result, or their explicit native,
original/current-environment, effects, oracle-law and release-artifact joins.
The <=2^-100 per-attempt target is not yet established.

The staged whole-packet whitespace check reports the preserved old harness's
trailing space and raw compiler-log trailing spaces/blank lines. Those pinned
evidence bytes are intentionally unchanged. The maintained Python and design
files pass their focused whitespace check.
