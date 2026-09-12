# Completion-pack intake and first source-transcript slice

Latest work: [same-body opened-query constructor and positive update](opened-query-constructor-20260912.md).
Earlier: [authenticated folds/residuals and later oracle histories](authenticated-fold-continuation-20260912.md).
Earlier: [same-body authenticated slots and FS prefixes](authentication-connection-20260912.md),
with historical-toolchain and patched-toolchain evidence kept separate.
Earlier work: [source connections and bounded FS scripts](source-connections-20260912.md).
Five new leaves passed compilation and a fresh kernel replay; full source/FS
soundness remains open. Earlier [2026-09-12 continuation](continuation-20260912.md) includes
same-body constructors, chronological commitment cuts, recorded C1 access and
a successful fresh kernel replay of the new ten-module closure. The material
below records the earlier intake slice, not the current total evidence.

This is an intermediate continuation, not closure of the same-body audit,
Fiat–Shamir security, or checked-payment extraction. Research branch:
`research/v8-completion-fs-extraction-20260911`, based on
`d5d0c8b4e60dad5e7b9c0bec6d41b143f04abe29`.

## Reproduction

From the repository root, run:

```sh
python3 docs/research/v8-completion-fs-extraction-20260911/check.py --stage python
python3 docs/research/v8-completion-fs-extraction-20260911/check.py --stage rust
python3 docs/research/v8-completion-fs-extraction-20260911/check.py --stage lean
```

`--stage all` runs those scoped stages, **not** all 26 supplied Lean drafts.
No network fetch is performed. Requires installed Lean 4.33.1 at commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Rust/Cargo and Python.
The runner rebuilds the two promoted first-party Lean leaves in a new temporary
directory, using pinned toolchain Std imports, and deletes the temporary artifacts
after hashing them. It does not reuse historical Aspis `.olean` files.
The supplied package's remaining Mathlib-dependent drafts remain uncompiled.
Linux/macOS time output records RSS and swaps; the runner also samples aggregate
child RSS and stops at 7 GiB/120 seconds. Lean has a 2048 MiB allocation limit.

`--stage kernel` returns **nonzero NOT RUN**, not success. Fresh kernel replay
belongs on a capped Linux scope with the reviewed explicit-module command.
External checking is not performed. No unchanged large replay was launched.

## What changed

- Reconciled the local repair: it constructs fixed-field projections, **not** a
  complete semantic `Program` from the authenticated body. The package's request
  to reuse a “completed repair” cannot be taken as evidence that one exists.
- Reproduced all 67 supplied Python tests and five release Rust controls.
- Imported the supplied sources with archive/member provenance. Historical
  packaged `results/` were not adopted as new evidence. Original zip remains
  unchanged in Downloads; hash is recorded in `archive-provenance.json`.
- Adapted `CausalPrograms` to Std and explicit universe parameters. Its universal
  across-continuation prefix theorem compiles; the interaction semantics and
  claim are retained. This generic theorem does not construct the Aspis strategy.
- Added `SourceSqueeze`: a **source-shaped**, chronological two-hash step using
  the actual `old_state || 1` and `old_state || 2` framing. Its producer fixes
  both input strings before either answer, retains full 256-bit answers, and
  has checked execution, request-order and distinct-domain identities.
- Compiled **actual** `field.rs`, `circle.rs`, and `transcript.rs` in an optimized
  standalone Rust executable. Checked short/long absorption, slice-partition
  equivalence, actual squeeze/advance input order, restored cache hits, and
  QM31/nonzero/q22 bounded-sampler failure and success controls.
- Fixed package integration's nested Cargo workspace error with a local empty
  workspace, without modifying the repository's production Cargo manifest.
- Repaired checker discovery: **do not call `leanchecker --help`**. Inspection of
  installed `LeanChecker.lean` shows unknown flags are ignored; with no module,
  it chooses the default project. The original command can start a large replay.
  The retained runner instead inspects the CLI source and requires finite Linux
  cgroup limits and zero swap before a fresh replay.

The Rust harness imports unchanged core modules by path. An unused KAT constant
`sumcheck::SUMCHECK_BYTES=112` is the only shim, checked against the source by the
runner. No semantic sumcheck or complete payment verifier is executed here.
The oracle is deliberately deterministic and full-answer/cached; it is **not**
SHA-256 or a measurement of random-oracle failure probabilities.

## Actual evidence

`results/v8-completion-fs-extraction-20260911/all-4ub41vwb/` preserves the initial
integrated run, including Cargo's workspace failure (exit 101). Its Python,
source-transcript and Lean checks passed. After the local Cargo fix, only the
affected Rust stage was repeated: `rust-9usj16hq/`, all passing.

The two focused Lean compilations took 3.03s and 0.49s including Lake/time
overhead, sampled aggregate peaks 685,760 and 530,752 KiB. Time logs record zero
swaps. Printed axiom lists contain only `propext`. Exact source/artifact hashes,
commands, output hashes and exits are in the JSON reports. These observations
are host proof-checking measurements, not prover timings or CU.

The local version's pinned upstream kernel source contains the opaque-value
free-variable check added by [upstream fix 7346219](https://github.com/leanprover/lean4/commit/7346219967957ca3dd4302a75a849b67eed1b3cd).
The corresponding source at [installed-version commit 819816b](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/kernel/environment.cpp)
was inspected. This is source/version evidence, not a rebuild or attestation of
the distributed Lean binary. Historical 4.32.0 evidence remains unchanged.

## Exact endpoint and premises

| Declaration/check | Constructed here | Remaining boundary |
|---|---|---|
| `CausalPrograms.execute_take_equal` | Equal coin prefixes preserve interaction prefixes for one legal program | Actual adversary/source state must produce that program uniformly |
| `SourceSqueeze.realised_execution` | A concrete two-request program and its chronological trace from state and oracle | Rust operational-semantics refinement is not proved |
| `SourceSqueeze.requests_fixed` | Both requested byte strings fixed across all continuations | Does not fix the entire V8 transcript early |
| `SourceSqueeze.input_domains_distinct` | Squeeze and advance inputs differ for any states | Does not imply globally fresh oracle inputs |
| Actual Rust harness | Byte inputs, order, cached restoration and exhaustion tested | Differential/source tests are not universal refinement |

No acceptance, candidate membership, recovered witness or terminal success is a
premise of these small declarations. Their inputs are a state, hash function,
coins and/or a causal program. They have no global acceptance conclusion either.
The `functional` definition returns output and new state; it is not defined by
ideal acceptance. Constructive nonvacuity is supplied by ordinary Rust source
executions, not a valid complete payment fixture for a new success predicate.

## Remaining obligation chain

1. Parse one actual body and execute the semantic/claim/response program from
   its consumed fields and public context. The old independent-`Program`
   interface is still insufficient. Retain its authentication theorem as a
   conditional helper, not full source closure.
2. Extend the source-shaped hash step to source-produced C1/C2 chronological
   cuts and all adaptive continuations; include cached calls, adversary prequeries,
   abort/retry/restore behavior and exact selected research framing.
3. Prove literal-source-to-functional execution, and a distributional coupling
   for the actual sampler and adversary, not just a pure hash equality.
4. Construct permitted-access circle/QM31 recovery and checked payment witnesses.
   Algebraic recovery and generic Gao/BW tests do not provide this.
5. Compose the charged authentication/recovery/FS events, then establish full-view
   adaptive ZK and all-reachable CU separately.

**Next decisive task:** construct the same-body semantic program producer through
the first OOD boundary from the selected `performance_verifier` path. Use actual
parsed fixed fields and early commitment state. Do not take a caller-supplied
semantic program or full-transcript callbacks as the producer.

## Verdict

| Gate | Status |
|---|---|
| Supplied Python and release Rust controls | PASS, limited to their reference models |
| Actual source-transcript deterministic controls | PASS |
| Two focused first-party Lean leaves rebuilt | PASS, toolchain Std cache reused |
| Axiom hygiene of those leaves | PASS, `propext` only |
| Full same-body functional construction | NOT COMPLETE |
| Across-history Aspis causal-prefix construction | NOT COMPLETE |
| Literal Rust refinement / FS coupling | NOT COMPLETE |
| Historical first-party closure rebuild | NOT RUN |
| Fresh kernel replay / independent external checker | NOT RUN |
| Allowed-access checked payment extraction | NOT COMPLETE |
| Global probability / adaptive ZK / all-reachable CU | NOT COMPLETE |

No protocol, proof format, acceptance, deployed identity or production source
changed. Body cap remains 40,282 bytes. Grinding security credit remains zero.
No new global security claim is supported. This is self-review, not an independent
cryptographic review. No push, merge, deployment or network transaction performed.
