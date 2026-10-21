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

## Remaining stages

Formatter/panic unreachability, concrete outer transport and all-family shared
oracle coverage remain to be investigated. No shipped Rust, key, peer-owned
source-identification or runtime-join file is changed.
