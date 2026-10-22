# CT field kernels — 2026-10-22 adoption candidate

Status: **not adoptable; frozen-artifact gate fails on the starting revision**.
Branch `codex/cx-ct-kernels-20261022`; baseline
`87545bd40543d6189f3aff8be6d3391759ea2dd7`; design-first commit `9ec2d749b`,
implementation snapshot `e2ffc6bbf`, followed by focused evidence/harness work.
No merge, push, Lean invocation, protocol change or deployment.

## Established scope

Default-off `ct-host-prover` selects arithmetic masks for M31 add/sub/neg,
64/128-bit reduction and zero tests. Existing mul/square and tower kernels
inherit these leaves; CM31/QM31/WideExact zero conjunctions evaluate eagerly.
WideExact raw normalization and scalar normalization use full-width folds
instead of remainder. Original verifier function bodies and line numbers
are preserved; candidate definitions are appended. The feature is rejected
on Solana, with program-build, and with incompatible arithmetic audit modes.

Production CT builds omit VALUES and CHECK_TIMES TLS storage. `trace::value`
is a no-op; both take APIs return empty vectors. The checker still computes
its local durations; removal of its phase control flow is not claimed.
`ct_fixture_gate` asserts empty TLS collections after each actual proof.

Evidence: `../evidence/ct-kernels-20261022/`. Source checks are lexical/byte
checks, Kani results are symbolic source results, native tests and fixture
measurements are separate. None establishes compiler/CPU constant time.

## Symbolic gates and their domains

`tools/ct-kernels-20261022/lib.rs` imports the actual aspis-core and an
exact baseline field snapshot (only its module path attribute is relocated).
The accepted gate list in `gates.json` identifies 69 distinct Kani harnesses:

- Seven leaf equivalences: reduce64/reduce128 on every u64/u128; add/sub/neg
  on every canonical operand; zero on every raw u32; raw-u32 normalization
  against the original `% P` expression.
- Twelve direct CM31/QM31/WideExact add/sub/neg/zero equivalences.
- One M31 multiplication composition and eleven CM31/QM31/WideExact
  multiplication, square and mixed-product compositions.
- Two canonical-output gates and one raw eight-limb constructor gate.
- Seven base-kernel, twenty-three tower-operation and five mixed-operation
  two-run trace checks, with independently chosen canonical operands.

The nonlinear composition is bottom-up, not an unproved replacement of a
primitive. The reference run records operation identifiers, complete operands
and arbitrary canonical results. The candidate must request exactly the same
operations/operands, consume exactly the same record and return the same
result. Every legal deterministic leaf implementation is an instance of this
stronger paired-oracle contract. The base equivalences plus output-range
checks discharge M31 boundaries; the CM31 results discharge QM31 boundaries;
the QM31 results discharge WideExact boundaries. Finite oracle capacities,
all memory accesses and unwinding assertions are checked. The 512 Rust macro
recursion setting is solely in the isolated Kani harness, for expanding
multiple stub attributes; no Lean resource setting was added.

`instrument.py` mechanically copies the actual CT leaf bodies and inserts
entry/expression events. Its restricted source check rejects control flow,
indexing, short-circuit operators, division/remainder and unreviewed calls.
The tower checks execute the actual tower methods with these instrumented
leaf implementations as stubs. Record/replay compares each emitted event
online and then checks equal length; its mode branch is public harness
instrumentation. Arithmetic comparisons are L2 atomic operations, not claims
about their native instruction selection. Fixed field offsets and absence
of allocations in these kernels are source facts; allocator/whole-prover
trace equality is not proved here.

The final trace-family replay also checks the base recorder's compared-prefix
bound. Kani's substring selector matched 35 trace harnesses; all passed. The
coverage list counts distinct harness names, not repeat executions.

The canonical domain is material: publicly constructible raw M31 tuples can
make the original add/sub/neg overflow or panic. The candidate's wrapping
helpers do not claim identical invalid-input panic behavior. No universal
whole-prover equivalence or whole-prover L2 result follows from these local
results. Canonical decoder/derived-equality guards and zero-sensitive
inv/try_inv remain outside this stage's constant-trace claim.

## Native validation and measurements

The existing field regression suite passes: 41 tests, optimized, including
independent polynomial multiplication oracles, inverse roundtrips and raw
constructor cases. These are tests, not symbolic proofs.

The timed diagnostic example uses the existing deterministic S2 transfer
and withdrawal fixtures and the actual P_R1 check. Both complete 57,607-byte
proofs compare byte-for-byte on the host, pass strict tx1/tx2 and the dense
verifier, and have identical public bytes. Proof SHA-256:

- Transfer: `eaaf4bfff6c5ee992f41f031bea02c46f48b6ace64cc716196a3d1d5f92400a2`.
- Withdrawal: `fc5499f1ae7fc6e2763e4bc174dfa3315cc79917d4be78dd4d9fa5b8f66cc286`.

| Fixture | Baseline prover s | CT prover s | Change |
|---|---:|---:|---:|
| Transfer | 41.7381 | 39.0071 | -6.54% |
| Withdrawal | 38.9356 | 42.2251 | +8.45% |

These are **single-run fixture measurements**, including P_R1 and excluding
fixture preparation and verification; other host work was present. They
establish neither a speedup/slowdown bound nor side-channel non-detection.
The complete timed-suite process walls were 80.7184 and 81.2808 seconds.
Native binary hashes, features, CPU/OS and toolchain are in
`fixture-identities.json` and `environment.json`. The CT binary has neither
VALUES nor CHECK_TIMES symbols; the baseline has both. This symbol check and
the empty-take assertions corroborate the cfg storage removal.

## Frozen artifacts: blocking result

| Mode | Required pin | Candidate result | Bytes | Frozen identity |
|---|---|---|---:|---|
| Default verifier | dfc2a91a… | 40dc7574… | 1,508,152 | FAIL |
| Devnet verifier | fb2fc048… | 12cb0bc2… | 1,508,152 | FAIL |
| Pool | 121f3e29… | 121f3e29… | 605,704 | PASS |

Full SHA-256 values and exact commands are in `elf-identities.json` and the
final `elf-v5-*` receipts. Each build exited 0 with zero swaps: default
26.236 s / 647,008 KiB peak RSS; devnet 2.390 s / 203,436 KiB; Pool
25.977 s / 644,460 KiB. The candidate's disabled-feature field bodies recover exactly
to the baseline at their original line numbers (`source-check.json`). No
program or statement source was edited by this branch.

A reproducibility hazard was found while isolating this mismatch: sharing
our private target cache across copied source snapshots with older preserved
mtimes can reuse stale project objects. The first frozen-source control is
therefore **invalidated**, not evidence of a frozen-source mismatch. Refreshing
only owned project-source mtimes forces recompilation while preserving the
registry cache. The refreshed frozen-source control reproduces the required
`dfc2a91a…` ELF under the same toolchain/flags. Final candidate ELF receipts
use this invalidation before rebuilding all modes; baseline controls are
recorded separately. Fresh baseline default/devnet artifacts are byte-for-byte
equal to the final candidate artifacts (`baseline-identities.json`). The
frozen-source control and invalidation are in `cache-control.json`. No other
worker's cache or source was modified.

The starting revision has shared-source changes relative to the accepted
ASQ8 frozen-source workspace, including fast_dots/fast_pairing/weights
(`inherited-source-differences.json`; a file inventory, not per-file causality). This
job does not adopt, revert or repair those other candidates. Even a match to
the starting revision does not meet the requested frozen pins. The lead must
reconcile the release source baseline and rerun the identity gate before
adoption; the required pins have not been relaxed.

## Resource, provenance and failed approaches

All Rust/Kani/SBF attempts ran on the dedicated host in our own directory,
with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and four Cargo
jobs (one Kani solver at a time per scope). Resource reservations were
checked against 55 GiB before launches. Native link flags are
`-C link-arg=-Wl,--threads=4`; SBF uses the frozen direct-lld spelling,
with a wrapper applying the native limit to SBF host build scripts as well.
Native runtime gates use release optimization; Kani's dev compilation uses
opt-level 3. Expected compilation versus proof generation/checker elimination
is recorded before each attempt. No memory cap was raised.

Native rustc/cargo: 1.94.1; Kani: 0.67.0; SBF build tool: 3.1.13,
platform-tools v1.52 / rustc 1.89.0. `environment.json` records full versions,
CPU and OS. These pin the fixture environment, not a deployed production
prover. No disassembly or dudect claim is made.

Every retained receipt records target/command, source revision label and
SHA-256 inputs, dependency fingerprint, exit, wall, GNU-time peak RSS,
cgroup peak memory, swap and limits. Timeouts can undercount descendant RSS
in GNU time; use the separately recorded cgroup peak. All recorded swaps
are zero. `#print axioms`: N/A for every gate; no Lean theorem was compiled.
`candidate-inputs.json` supplements early receipts with build/source inputs;
`gates.json` indexes accepted and failed attempts. Early revision labels
include dirty snapshots; per-attempt hashes distinguish those sources.

Failures are retained: initial harness module resolution; trace equality's
memcmp unwind bound (replaced with bounded element comparisons); cold SBF
host-linker task exhaustion (bounded wrapper); missing checked-in KAT inputs
(restored); Rust stub-macro expansion depth (isolated harness setting).
The initial broad composed tower attempt timed out at 180 s, and the
base-leaf-only QM31 composition timed out at 90 s. Their replacements use
smaller already-proved CM31/QM31 boundaries, not a larger memory cap or
longer unchanged run. Sampler/sparse/query/multiproof/checker algorithm
rewrites and Lean builds were not started.

## Remaining work and handoff

This closes local arithmetic equivalence and the stated kernel trace checks,
with fixture byte preservation. It discharges no end-to-end cryptographic
premise: E1/E2 and the existing privacy/refinement hypotheses remain. It does
not transfer earlier Lean source-helper proofs automatically to this new
feature set. The lead must re-pin/recheck prover refinement dependencies;
verifier release claims cannot pass until the artifact mismatch is resolved.
The complete L2/100-bit privacy target is **not yet established**.

Next implementation items, each with its own note and gates: sampler
remainder/division and circle fallback; sparse_eq_weights fixed-shape
traversal; QueryScan duplicate handling; multiproof sibling sharing; P_R1
checker elimination/pivots. Also retain canonicality/equality/nonzero caller
invariants, constant-work inversion/try_inv validity handling, the L1 joint
retry law, and the L3 compiler/CPU trust and measurement obligations. The
simulator is outside this candidate. Generated build keys remain retained on the host with mode 0600; no key
cleanup, live RPC or fund operation was performed.

Local source/document whitespace checks pass with raw tool logs excluded;
those logs are retained verbatim, including compiler whitespace. The source
provenance/instrumentation audit and consolidated evidence audit exit 0.
