# R72: actual sampler extraction and outer-loop execution

Base revision: `bc92dd5675b58ba3076b999429f7cbdfc6675baf` (R71).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Exact boundary

The selected, unchanged `transcript.rs` now extracts and compiles together with
its actual field/circle closure: **49 functions, zero opaque extracted
functions, ten types, zero generated external templates**. `Result::map_err`
is extracted from the pinned Rust standard library, not supplied as an axiom.

Eleven new theorems prove the generated outer circle-sampler loop equals a
finite recursion on its remaining U32 range length. The actual public entry
uses exactly three candidate slots. This recursion calls the **actual generated
`challenge_qm31` and circle map**, not replacement sampling/mapping functions.
No hypothesis that those calls succeed, terminate, or sample uniformly is used
by the loop equivalence. Their internal failure/divergence is preserved.

Corollaries establish zero-fuel outer exhaustion, immediate inner-exhaustion
propagation, immediate successful return, and continuation from the advanced
transcript state after a rejected successful parameter. The latter does not
restart from the prior state. These are exact source-control-flow results;
they do **not** yet prove inner byte decoding, canonical draws or hash traces.

## Important axioms-audit qualification

The generated sampler references the cached runtime's `unwrap` via the slice
to four-byte-array conversion. That runtime declares
`axiom core.fmt.Formatter : Type`, because its `Debug` trait signature mentions
the formatter. The runtime `unwrap` implementation ignores its `Debug`
argument and returns the value or `.fail .panic`; no formatting is performed
by that model. The relevant runtime source is pinned in the evidence.

Consequently eleven of the fourteen theorem/definition audits include this
**inherited opaque type declaration**, besides standard Lean axioms. There
are no newly declared axioms, admitted proofs or new hiding assumptions, but
this is **not a standard-axioms-only result**. The audit is deliberately marked
`PASS_SCOPED`, with this dependency visible. No claim is made that the Rust
formatting backend is refined or that the sampler cannot panic. Proving safe
four-byte slicing and conversion on every reachable inner state remains part
of the next obligation; a stricter erased-formatting correspondence, if needed,
must be proved rather than changing the cached runtime silently.

## Source pins and diagnostic attempts

The extractor validates all 202 selected R69 stage pins, copies the crate
sources unchanged, and adds only a public extraction entry to `lib.rs`.
A dependency-free standalone Cargo manifest is used with release overflow
checks enabled. The actual build script is additionally pinned to
`7905b8c2a92c72a79a8a6c785a91ce162fb338569a02867f671d1910e21b6e0d`;
its local repository bytes and selected-stage bytes agree. It generates the
tables needed to typecheck the complete crate; no table or unrelated protocol
operation is made a sampler assumption. Staged Lean changes only imports.

Retained attempts:

- The first extraction setup omitted the build script and failed Rust
  typechecking (`OUT_DIR` missing), before producing usable extraction.
- Including `core::option` alone extracted successfully but emitted a
  `map_err` axiom template, which was not accepted as a proof input.
- Broadly including `core::result` exposed an unsupported enum expansion at
  standard-library `result.rs:2194`; translation exited 2.
- Including only `core::result::_::map_err` resolved the template without that
  unrelated expansion. Charon and Aeneas both exited 0, without source edits.
- An initial local transfer missed its destination directory; the generated
  compilation attempt failed before the files were present. Fixed staging
  compiled both leaves. The first outer proof needed a U32 maximum alias
  normalization and matching normalization of the induction hypothesis; the
  corrected proof compiles without raising heartbeats.

All failures remain diagnostics, not release passes. No OOM/retry with a
higher memory cap occurred.

## Compiled/measured evidence

Pinned Charon SHA:
`b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`.
Pinned Aeneas SHA:
`e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813`.
Rust `nightly-2026-06-01`; Lean `leanprover/lean4:v4.32.0`.

NUC scopes: `MemoryHigh=5 GiB`, `MemoryMax=7 GiB`, `MemorySwapMax=0`,
`TasksMax=128`, recorded from the actual cgroup. Lean uses `-j1 -M4500` and the
pinned cached workspace. Smallest leaves first, one final replay of the three
targets, 319 prior targets reused. No package-wide dependency rebuild.

| Exact target/job | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Selected Charon sampler extraction | 0 | 10.62 | 604,100 | 0 |
| Selected Aeneas translation | 0 | 1.21 | 116,512 | 0 |
| `AspisR72Sampler/Types` | 0 | 1.22 | 2,543,592 | 0 |
| `AspisR72Sampler/Funs` | 0 | 2.18 | 2,570,924 | 0 |
| `AspisV8R19/SamplerOuterExecution` | 0 | 2.10 | 3,708,220 | 0 |

Eleven theorem audits plus three generated-definition audits are recorded.
`map_error` has no axioms; `range_next` and `squeeze_block` have only standard
Lean axioms. The other eleven include the inherited opaque formatter type.
The source/dependency checker verifies all 283 final dependency pins; 126
public evidence artifacts are indexed in `evidence/r72-sampler/MANIFEST.json`.

Audit command:
`python3 docs/research/v8-full-view-zk-20260912/tools/check_r72_evidence.py`.

## First remaining proposition

Prove the generated **squeeze/byte/limb sampler** corresponds to the retained
memoized shared-oracle program, preserving exact input frames, safe four-byte
slicing, little-endian decoding, P rejection, block rollover, the eight-attempt
per-limb limit, and all state/trace observations. Transport R71's circle
semantics to the R72 generated namespace and compose with the outer theorem.

The hash function parameter in extracted execution returns `Aeneas.Result`;
totality and source/hash-oracle correspondence cannot be silently assumed.
The deterministic execution bridge must precede any fresh-answer probability
claim. Known shared-oracle inputs are not independent fresh draws.

Full seed/C2/joint-view simulation, visible failures/retries/publication,
numerical privacy loss and coherent pre-beta soundness extraction remain open.
C1's negative regression, fixed-block hiding, local joint coverage and global
privacy stay separate. No full privacy/soundness or verified compiler claim.

No runtime/protocol change or new CU benchmark: retained complete verifier CU
is **1,495,663 / 1,497,050**, and both actual 1M runs still exhaust. No merge,
deployment or wallet operation; no keys or private fixtures collected.
