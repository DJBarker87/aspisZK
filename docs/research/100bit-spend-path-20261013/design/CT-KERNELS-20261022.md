# CT field kernels — 2026-10-22 adoption candidate

Current candidate: **v2**, branch `codex/cx-ct-kernels-v2-20261022`; see the
v2 section below. The stage-2 report below is retained evidence.

Historical stage-2 status: **unmerged adoption candidate (LOG D162, D163); retained ELF identity gate PASSES against the user-approved S4 release pins**.
Branch `codex/cx-ct-kernels-20261022`; baseline
`87545bd40543d6189f3aff8be6d3391759ea2dd7`; design-first commit `9ec2d749b`,
implementation snapshot `e2ffc6bbf`, followed by focused evidence/harness work.
Research merged before Stage 3; no push, Lean invocation, protocol change or deployment.

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

## Frozen artifacts: corrected release-pin comparison

| Mode | Required pin | Candidate result | Bytes | Frozen identity |
|---|---|---|---:|---|
| Default verifier | 40dc7574… | 40dc7574… | 1,508,152 | PASS |
| Devnet verifier | 12cb0bc2… | 12cb0bc2… | 1,508,152 | PASS |
| Pool | 121f3e29… | 121f3e29… | 605,704 | PASS |

Correction (2026-10-22): Session A’s user-approved S4 adoption, commit
`29cbab431` and `S4-ADOPTION-DECISION-20261022.md`, superseded the old
`dfc2a91a…` / `fb2fc048…` pins. The candidate builds already match the
approved default `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0`,
devnet `12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f`,
and Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
The earlier blocker was an incorrect comparison to superseded pins, not drift.
Historical receipts remain unchanged.

Full build SHA-256 values and exact commands are in `elf-identities.json` and the
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

The inherited S4 fast_dots/fast_pairing/weights changes are approved research
source. `inherited-source-differences.json` is a historical inventory, not
evidence of release drift. No artifact mismatch remains against the new pins.

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
the corrected artifact comparison passes, while the remaining adoption gates stay open.
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


## V2 — secret operands and D166 simulatable traces

Status: **PASS at the documented local source/compositional boundary;
unmerged adoption candidate.** All requested release identity and fixture
measurement gates pass. This section supersedes the
old remaining-work list. Research base `c6be35873e`; branch
`codex/cx-ct-kernels-v2-20261022`. No merge, push, Lean, deployment or live RPC.

Stage 2 is retained through cherry-picks `7d6494967d` (e2ffc6bbf),
`4d5e610c18` (stage-2 evidence and completed harnesses), `50dea2e10d`
(ELF-pin correction), and `e303eb3f8d` (corrected executable gates).
Pole implementation/proof harness: `47999f105f`. Stage 3(a)–(e) and the
checker assessment stay exclusively on `codex/cx-ct-kernels-20261022` as
measured historical evidence. `v2-source-audit.py` checks their commits are
absent from v2 ancestry and their production files recover to research.
The unchanged prover.rs differs from research only by stage-2 TLS gating.

### Constant-trace secret-operand scope

With `optimized-terminal,ct-host-prover`, the following source operations have
the stated constant-trace boundary on canonical field operands and a fixed
valid public layout. Integer comparisons/bitwise operations are L2 primitives;
compiler lowering and instruction latency remain L3 obligations.

- `crates/aspis-core/src/field/ct.rs:8`: M31 conditional subtraction,
  full-width u64/u128 reduction, add/sub/neg and zero test. The existing
  M31 products/reduction, CM31/QM31/WideExact arithmetic and eager tower
  zero tests inherit those leaves, exactly as documented in stage 2.
  `field/wide_exact.rs:632` normalizes raw u32 limbs without remainder.
  The v2 audit binds these sources to the retained stage-2 Kani evidence;
  unchanged arithmetic gates are not rerun.
- `crates/aspis-r1-cost-probe/src/host_semantic.rs:314`
  `lean_copy_row_values`: fixed registry-driven tuple bank/row/column/slot
  accesses, 16 limbs per endpoint, CT M31 offset addition, and CT QM31 row
  accumulation. Registry construction/arity checks, allocation lengths and
  error paths depend on public geometry; this claim is for valid fixed shape.
- `crates/aspis-statement/src/logup.rs:75` `compress_tagged_tuple`:
  tag lifting, 16 iterations on this pole path, QM31 multiply-by-M31,
  addition and power multiplication inherit the CT kernels by Cargo's shared
  aspis-core feature. Its exact body and `lift` are unchanged from research;
  there is no new verifier-side implementation.
- `crates/aspis-r1-cost-probe/src/host_semantic.rs:285` routes the CT
  `no_pole` verdict to `ct_pole.rs:5,14,18`: raw four-limb XOR/OR equality,
  eager boolean verdict folding, and every row/side/slot in order. There
  are **4,096 comparisons**, including inactive/empty slots; public active
  masks are folded into the result. No secret-dependent short circuit or
  pole-position early exit occurs. The final pole bit still controls the
  existing retry law; constant trace does not remove that L1 obligation.
- `crates/aspis-r1-cost-probe/src/trace.rs:6,18` and
  `prover.rs:295,301,317`: CT builds omit VALUES/CHECK_TIMES TLS storage;
  value logging is a no-op and take APIs return empty. Local checker timers
  and the challenge-dependent checker remain as before.

No general constant-trace claim is made for decoders, derived equality outside
the pole helper, inv/try_inv validity selection, invalid witness checks, or the
whole prover. Their existing canonicality, nonzero and honest-input invariants
still need the lead's refinement/trace justification. The helper's nonzero
inversion domain follows only when the existing no-pole precondition is met.

### Pole equivalence and trace evidence

`pole-instrument.py` copies the actual comparison/scan and compression bodies
and inserts events at expression sites, public row/side/slot accesses and
compression iterations. It fails closed on changes to the approved body
shapes and verifies the row reader and compressor are unchanged from research.
Fixed field offsets are audited; calls into the field kernels use the retained
stage-2 trace results. Events are generated from owned source, not a separately
invented expected schedule.

Six Kani gates pass: raw-u32 QM31 equality equivalence; arbitrary-state
clear/active fold equivalence; arbitrary two-row scan equivalence against the
old active-only loop; two-run scan traces with independent raw operands;
16-limb compression equivalence; and two-run 16-limb compression traces.
The compression equivalence is paired-oracle composition at the already-proved
QM31 add/mul/mul_m31 boundaries: both runs must issue the same operation with
all the same operand limbs and consume the same arbitrary canonical result.
It is not a second nonlinear bit-blast of the tower multiplication proof.

The scan proof is compositional: the arbitrary clear/active/value one-step gate
preserves the old fold, so induction over the public traversal preserves its
verdict. The two-row Kani trace result plus the checked public-only loop/index
structure supports repetition at fixed public shape. Kani does **not** unroll
the 1,024-row witness reader or prove whole-prover trace equality.
The optimized native test independently replays the full 1,024-row scan,
counts all 4,096 comparisons, and checks late/first poles and inactive masks;
it also replays 16-limb compression with distinct inputs. Both existing
`no_pole_is_lean_no_pole_{transfer,withdrawal}` tests pass with the CT feature.
These finite tests are corroboration, not substitutes for the symbolic gates.

### F3/F5/F6 left to the simulatable-trace proof

D166 changes the obligation for challenge- and private-coin-dependent work:
prove that the **joint exposed trace** can be simulated, including rejected
attempts, duplicate candidates, failed prefixes, retry/exhaustion/error paths,
allocations, rank/collection history and the eventual public proof. It is not
enough to label successful-proof challenges public. No such end-to-end proof
is added by this candidate. The locations below are current v2 source lines,
not the audit's older line numbers. `probe` = `crates/aspis-r1-cost-probe/src`,
`prover` = `crates/aspis-prover/src`, `core` = `crates/aspis-core/src`,
`statement` = `crates/aspis-statement/src`, and `z4`/`c3` =
`docs/research/v8-r0-zk-20261009/{z4,c3}`.

| Item | File:line, unchanged algorithm | Trace law still required |
|---|---|---|
| F3 | `prover/state_only_entropy.rs:202` `generate_for_mask_nonce` | Up to 16 OS draws, nonzero seed comparisons/short circuit, error prefix; joint environment/seed law under E1. |
| F3 | `prover/state_only_entropy.rs:760,780,794,804` `Profile21SourceExpander::{new,next_word,m31,qm31}` | Refill positions, scalar rejection counts, four-limb early propagation and exhaustion, jointly with previously read ROM blocks. |
| F3 | `prover/state_only_hiding.rs:330,350,361,371` `SeedExpander::{new,next_word,m31,qm31}` | Same seed/refill/limb/rejection history for mask derivation; field arithmetic uses CT leaves but sampling control is unchanged. |
| F3/F6 | `probe/sim.rs:79,80,84` `Coins::{new,coin,nonzero}` | Simulator nonzero loops and coin-consumption prefixes, related to the real joint law rather than separately asserted independent. |
| F5 | `probe/sampler.rs:8,21,45,102,111,121`; `probe/r1_wire.rs:194,209,256`; `probe/transcript.rs:23,31` | Challenge rank division/remainder, gamma carry and circle singular/subfield/fallback selection. `core/circle.rs:34,55` and `core/r0_transcript.rs:177` retain challenge-dependent validity/fallback branches. |
| F5 | `statement/constraints_v4.rs:601,654,782`; `probe/host_semantic.rs:31,204` | Sparse ZERO/ONE suffix pruning, capacities, selected column addresses and point-claim interpolation, including prior FS coordinates. |
| F5 | `core/r0_transcript.rs:202,216,305`; `probe/transcript.rs:35` | Duplicate history, accepted positions, early stop, returned stream advance and QueryScan exhaustion, not just the published accepted list. |
| F5/F6 | `probe/prover.rs:253,266`; `probe/host_commitment.rs:220,229,242`; `probe/multiproof.rs:54,198,248,251` | Opening word/salt addresses, sort/dedup, sibling sharing, node lookups/counts, Vec growth and fixed-slot padding. |
| F6 | `probe/prover.rs:307,354`; `z4/z9e.rs:50,90,184,196` | P_R1 factoring through hidden-attempt challenges, certificate creation/checking, phase timers, caught panic and retry/error prefixes. TLS retention is disabled, but local phases and their work remain. |
| F6 | `z4/z9c.rs:107,135,290,332`; `z4/z9d.rs:17,41,74,90,113` | Zero skips, pivot searches, row swaps, inverse branches, rank thresholds, certificate-sized allocations/indices, early stopping, conversion and matrix-product work. |
| F6 | `z4/z9.rs:567,989,1010,1016`; `z4/z9b.rs:78,107`; `z4/probe.rs:2207,2214,2256` | Query-derived layout, lane counts/selection, relation functionals and raw/tail coefficient construction. |
| F6 | `c3/build/src/lib.rs:108,317,358,539,820,918` | The six `fill_*` entry points and their supporting arithmetic/selector/source loops, driven by challenge/certificate descriptors and dimensions. |
| F6 | `c3/check/src/lib.rs:27,40,56,81,96,138,149,160,171,182,193,204,215,227,243,255,270,275,370,384,407` | Dot/image/pivot/entry/product/identity/echelon/permutation/null-vector/lift/half checks, arithmetic helpers and checker entry points; certificate-dependent selection, work and failure prefixes. |
| F6 | `probe/sim.rs:99,114,133,358,368,396,439` | Full-byte BTree oracle-key comparison, insert/overwrite/collision/hit-set history, memoized opened/folded/leaf maps, parent sets, lazy callbacks and repeated-parent sharing. Existing functional collection laws do not prove their cost law. |

Stage-3 fixed-shape samplers, tensor weights, QueryScan and multiproofs are
not adopted into v2. No P_R1 checker rewrite or new simulator implementation
was attempted. L1 joint retry/statistical coupling, L2 simulatable-trace
transport/refinement and L3 compiler/CPU preservation remain distinct open
obligations; the 100-bit whole-prover target is not claimed closed.

### V2 artifacts, measurements and provenance

Evidence: `../evidence/ct-kernels-v2-20261022/`. The three fresh
`elf-v2final-*` builds exit 0 and reproduce the adopted pins exactly:

| Artifact | SHA-256 | Bytes |
|---|---|---:|
| Default | `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0` | 1,508,152 |
| Devnet | `12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f` | 1,508,152 |
| Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 605,704 |

Both actual 57,607-byte proofs and both 1,880-byte public encodings compare
byte-for-byte with the retained stage-2 baseline files on the host. They pass
strict tx1/tx2 and dense verification. Transfer and withdrawal proof SHA-256
remain `eaaf4bff…` and `fc5499f1…` as recorded above; complete hashes, public
hashes, binary hash and feature set are in `fixture-identities.json`.

| Fixture | Retained baseline prover s | V2 prover s |
|---|---:|---:|
| Transfer | 41.7381 | 38.5119 |
| Withdrawal | 38.9356 | 37.9546 |

These are single samples, measured around proof generation with P_R1 included,
excluding preparation and verification. They are near the approximately
40-second baseline; no performance bound or L3 timing result is inferred.
The complete v2 fixture process took 76.5101 s, peak RSS 551,008 KiB, zero swap.
The native binary is SHA-256
`33a759661fd7f43316d9c90e870dff6e2726324b4dabf909692405656d725450`.
Its resolved Cargo feature tree includes `aspis-core/ct-host-prover`; VALUES
and CHECK_TIMES symbols are absent, and both take APIs were asserted empty
after each actual proof. See `host-metadata.json` and `v2-feature-closure`.

All Rust/Kani/SBF jobs used the dedicated v2 host directory, the retained
private compiled cache, fresh owned-project source mtimes, release native/SBF
builds and optimized Kani compilation. Every launch reserved against the
55-GiB host budget and used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, four Cargo jobs and one solver at a time. The new receipts record
exact command/target, source label and SHA-256 inputs/dependency fingerprint,
exit, wall, GNU-time peak RSS, cgroup peak, swap, flags and toolchain/CPU.
`#print axioms`: N/A throughout; no Lean was run. Production source hashes
match implementation `47999f105f`; tooling refinements are separately pinned
by each receipt. The final native trace test strengthens the earlier native
sample with an explicit first-active-slot pole check; the earlier receipt is
retained, not silently treated as a new unchanged run.

Two launch/scope problems are retained in `attempt-notes.json`: the initial
unscoped `cargo test` compiled an unrelated integration test whose baseline
snapshot was absent in the host subset (exit 101); the focused `--lib` pole
regression passes. A copied historical `elf-v2-default` receipt caused the
first ELF launch to refuse its already-used name **before compilation**;
`elf-v2final-*` are the only v2 ELF release receipts. No cap was raised and no
unchanged completed full suite was replayed. All six new symbolic gates and
all accepted native/ELF/fixture/feature gates exit 0, with zero swap.

All old and new generated build keys remain on the host; the three new keys
are mode 0600. No key cleanup or fund operation occurred. No binaries, keys,
ELFs, tarballs or Lean objects are committed. The branch stays unmerged and
unpushed; this task stops after these gates and the v2 scope report.
