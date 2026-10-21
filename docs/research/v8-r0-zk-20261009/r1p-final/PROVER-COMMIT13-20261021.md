# Prover commitment continuation 13 — 2026-10-21

Branch `codex/cx-prover-commit13-20261021`, base `9f6852af9`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit13-20261021/`.

## Stage 1: explicit canonical admitted-domain endpoint

`ProverCommitAdmittedEndpoint` extends the `PrivacyR1HeadlineOwnedClosed`
namespace with an explicit `Admitted` endpoint. Its `input` is fixed to
`BuilderSource.prover`: the M31 public/witness pairs satisfying the embedded
`RspendPlus` relation, the canonical extracted merged trace, and S2 transport.
It does not claim that a shipped Rust runtime record has been identified
with that instance. That source identification remains peer-owned and open.
The original arbitrary-input endpoint is unchanged; the part-12 counterexample
remains valid there.

`Admitted.builder_premises` is proved from D96's canonical builder theorem;
`PhaseWireLog2Bin.honest` changes no public or build projection. The specialized
endpoint initially retains the premise to make the subsequent deletion-only
change reviewable. J8364 is an excluded missing-CharP elaboration draft.
J8365 passes the focused endpoint and all three printed axiom audits using
only the standard three axioms: exit 0, wall 6.97 s, peak RSS 4159700 KiB,
zero swaps. Exact source/dependency hashes and source revision are in the
receipt. No package-wide build or unchanged regression is run.

The canonical builder theorem now uses an implicit statement parameter, so
its name resolves to the proved theorem after deleting the identically named
premise. J8366 is an excluded doc-comment placement draft; J8367 checks the
specialized before statement (exit 0, 6.82 s, 4158164 KiB, zero swaps).
J8368 checks the deletion-only after statement (exit 0, 6.71 s, 4161568 KiB,
zero swaps), with all three audits standard-axiom only.
The full verbatim texts are `headline-specialized-before.lean.txt` and
`headline-specialized-after.lean.txt`; `headline-deletions.diff` deletes exactly
one binder, with no other change:

```lean
-- Before (verbatim)
theorem privacy_headline_admitted
    (builder_premises : BuilderPremises h B x)
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
```

```lean
-- After (verbatim)
theorem privacy_headline_admitted
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
```

This is genuine discharge on the explicitly fixed canonical domain. It is a
specialization of the previous arbitrary-input theorem, not a weakening with
unchanged quantifiers. The experiment, error bound and remaining real/ideal
execution-join premises are byte-identical between the two specialized texts.
No runtime join or successful-source admission proof is added or hidden.
Shared Env J drafts/objects were snapshotted under this branch's own host
directory before replacement; no peer-owned module was replaced.

## Stage 2: actual stream panic and formatter safety

The actual `SeedExpander::next_word` and `Profile21SourceExpander::next_word`
bodies run with arbitrary seed, counter, buffered bytes and `word <= 8`,
including counter wraparound and buffer reload. Constructor `word = 8` is
inside this domain; the checked postcondition retains `1 <= word <= 8`.
The oracle table holds arbitrary answers; this is a deterministic bounded
expander oracle, not a SHA-256 or probability assumption.

Two checks run each body without a formatter stub, retaining all Kani safety
and unwinding checks. Two subsequent checks use
`#[kani::stub(<core::array::TryFromSliceError as core::fmt::Debug>::fmt,
formatter_never)]`. The replacement first asserts false and then diverges:
reaching it fails verification, rather than assuming the path unreachable.
Thus the stub does not erase a reachable error. The slice is always exactly
four bytes and within the 32-byte block. These Kani checks avoid adopting
part 12's forbidden extracted Formatter dependency; no tainted Lean theorem
is imported as justification.

| Exact suffix under `safety13` | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| `state_only_hiding::...::mask_next_no_panic` | 0 | 8.920 | 551672 | 0 |
| `state_only_entropy::...::source_next_no_panic` | 0 | 11.295 | 659604 | 0 |
| `state_only_hiding::...::mask_next_no_formatter` | 0 | 10.874 | 659256 | 0 |
| `state_only_entropy::...::source_next_no_formatter` | 0 | 11.113 | 659340 | 0 |

Receipts record complete names/commands, source hashes, cgroup peaks,
6G/8G/no-swap/64-task limits, and required linker flags. `#print axioms` is
not applicable to Kani; the only new Lean endpoint remains standard-axiom
only. Expected time is compiler and bounded-verifier work, not native dense
arithmetic. The actual Rust bodies are unchanged in the proof snapshot;
only proof harnesses are appended. No production Rust/Cargo file is edited.

The first draft omitted the next-word contract's table-domain setup and
failed its precondition (not a protocol counterexample). The second failed
an unwind check in `memcmp` because 34 was shorter than a domain string;
the accepted replacement increases only the harness's unwind bound to 84.
Exact excluded and accepted text snapshots are retained. No failed safety
check is treated as a success. Host sources and caches are cloned from
part 12; replaced sources use atomic rename to preserve the predecessor.

This closes these two local conversion/panic paths. It does not prove every
formatter or panic path in the entire shipped outer prover unreachable.
The actual scalar caller partition and complete query caller cut are the
next focused checks; they do not yet have accepted results.

## Stage 3: full query caller around the sampler boundary

`transcript::query13::result_and_retained_state` executes the complete actual
`Transcript::queries` method, rather than the part-12 prefix. Its observer
checks all seventeen hash calls, their exact state chain, row-31 framing,
payload pointer/length and both eight-block arrays. A sampler callee cut
checks those arrays and returns arbitrary queries/selected state or an error.
The actual caller forwards the successful query array and selected state;
on error it maps the error to `Transcript` and retains the absorbed state.
Both branches call the sampler exactly once. The trace hook is compiled out
in this library feature configuration, as it is without `prover`; the host
prover's optional trace side effects are not certified by this check.

`transcript-query-caller-v2` passes: exit 0, wall 17.524 s, peak RSS
547220 KiB, zero swaps. The v1 comparison bound 84 is shorter than the
88-byte query array; its unwind failure is retained and replaced by 170.
All safety and unwinding assertions remain enabled. The sampler cut is
explicit, not a verified sampler implementation or a probability law.
It proves the caller transport universally over its outcomes and supplies
the concrete array/result/state boundary for separately composing the
existing sampler proof. It does not replace the whole shared-oracle or
shipped outer execution join.

`ProverCommitScalarPartition.first_accept_partition` proves symbolically
that a sequence bounded by the rejection value has a first success or
exhausts. `sixteen_partition` specializes it to the seventeen scalar cases.
J8369 passes both audits with `[propext, Quot.sound]`: exit 0, wall 1.40 s,
peak RSS 2550616 KiB, zero swaps. No concrete recurrence or large carrier
is reduced. The direct `state_only_hiding::scalar13::mask_scalar_partition` check
subsequently passes: exit 0, 557.458 s, peak RSS 3234648 KiB, zero swaps.
This is one actual shipped scalar execution with no scalar/next-word stub.
Its seventeen-way partition constrains earlier candidates to rejection and
checks the returned value/error, seed, counter (including wraparound),
buffer and word position against a closed-form consumption specification.
The associated Lean lemma establishes exhaustiveness of the cases. The
Debug formatter stub asserts false before divergence, so reaching it would
fail this complete scalar check as well. The counter-indexed oracle table
contains arbitrary answers; it is not fresh independent sampling per word.
The proof has a different shape from the old two-execution timeout and was
not rerun after passing. The corresponding source-scalar run is distinct
and still pending. Whole material-builder transport remains open.

## Stage 4: actual material extraction and demonstrated obstruction

After proving the scalar safety boundary, the extractor is run on the actual
`build_mask_material_for_layout`, leaving only the actual m31/qm31 and
balancing helper calls opaque. This is a compositional cut, not a change to
the production body. The exact Charon command and all source/tool hashes
are retained. It uses `--release --jobs 4` and a copied, isolated Charon cache.

`material-charon-v1` succeeds: exit 0, 32.189 s, peak RSS 683432 KiB,
zero swaps; LLBC `has_errors=false`, SHA-256
`9c67eeabce7e541c4bb819f96bdb318ec8b33f7375257744195bfac0b3629a0a`,
size 1912945 bytes (binary/intermediate stays on the host).
`material-aeneas-v1` then fails: exit 2, 2.247 s, peak RSS 128832 KiB,
zero swaps. The exact error is:

```text
Unexpected
Source: 'crates/aspis-prover/src/state_only_hiding.rs', lines 471:4-489:1
Compiler source: interp/InterpAbs.ml, line 191
```

The stack reaches `InterpJoin.join_ctxs` / `convert_value_to_abstractions` at
the material-builder loop join. This is a new concrete outer-translation
obstruction after isolating the scalar/formatter cone. It is not a Lean
counterexample, a memory failure, or a certificate of the outer caller.
The unchanged failing translation is not rerun and no cap is raised.
The replacement deliverable is an owned, indexed material-loop reference,
with per-iteration Kani equality for the shipped iterator/`?`/Vec update and
Lean induction over that reference, then composition with the accepted
scalar/window and balancing laws. Failed extraction is explicitly excluded.

## Remaining stages

Formatter/panic unreachability, concrete outer transport and all-family shared
oracle coverage remain to be investigated. No shipped Rust, key, peer-owned
source-identification or runtime-join file is changed.
