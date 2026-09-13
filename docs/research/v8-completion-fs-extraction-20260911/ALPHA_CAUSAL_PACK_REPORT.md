# Alpha causal pack: exact request cuts

Date: 2026-09-13
Branch: `research/v8-completion-fs-extraction-20260911`
Starting source revision: `85e85e60f2124dc2bc1f5e170a5981cb8febc56b`
Pack: `aspis-v8-soundness-alpha-causal-pack-20260913.zip`
Pack SHA-256: `8787de4a0b42398367e9bcc9cf7fdd151c86bcf2a4de59d65b7bed21e8c504db`

## Bounded result

This continuation proves the missing **positional request-cut** part of the
alpha source bridge.  Given a positional fresh query in the returned V8
verifier trace, it constructs a single scheduler-native fresh request whose
state retains the full cached-inclusive history.  It also retains literal
history decompositions before and after that request, rather than merely a
list of fresh answers.

`returned_v8_verifier_query_has_global_native_request_with_exact_cuts` lifts
that construction through the actual V8 adversary-to-verifier callback.  Its
root cursor is advanced by the actual adversary fresh answers and the exact
preceding verifier answers.  No target, probability, selected-profile, or
source-alignment premise was added.

`scheduler_relation_alpha_label_of_exact_verifier_fresh_request` proves the
request-local deterministic half: when the cursor is the constructed verifier
fresh request, its alpha router label is exactly
`relationAlphaPreferredSlotFromHistory round state.history input`.  The
history is deliberately not projected down to fresh answers, so cached
records remain visible.

This is not yet the pack's final ordinary-slice inclusion.  The following
source refinement is still necessary:

```
positional root-trace fresh record
  -> exact chronological root trace prefix and suffix
  -> the same OracleState.history used by the native request
  -> equality with the corresponding Alpha0RootLabeledTrace record/position
  -> no earlier selected alpha label and router-coordinate realization.
```

Existing `FSV8ReturnedRootFreshTracePrefix` supplies a projected fresh-record
prefix, while `FSV8AlphaRootLabeledTraceConstructor` labels a separately
selected exact-root prefix.  Neither identifies each cached-inclusive
`OracleState.history` at a root trace cut.  A fresh-list equality cannot prove
this: cached lookups emit no fresh record but change (and are retained in) the
history.  The new local label theorem therefore cannot honestly be applied to
the whole-root labels yet.

## Retained open obligations

| Obligation | Status | Why it remains open |
|---|---|---|
| Exact root-history / alpha-labelled-record refinement | OPEN | No theorem identifies the native request's cached-inclusive `state.history` with the record at the selected whole-root alpha cut. |
| Selected profile `n + m <= 108`, alpha-prefix length, and `adversaryFuel <= q1` producers | OPEN | `FSV8ExactRootCursor.Configuration` exposes arbitrary fields; no selected work-script constructor produces these facts. |
| All-reached-output-fresh ordinary slice | OPEN | Router realization consumes `Alpha0RootLabeledTrace`; the preceding root-label equality and selected-prefix fact are unavailable. |
| Cached output / restoration branches | OPEN | They are not fresh router coordinates and require creator/restoration provenance. |
| First-block fallback cap | OPEN / unused | No source-specific invocation/fork cap is proved. |
| Fiat--Shamir lift and global probability composition | OPEN | This pack establishes deterministic cut construction only. |

No protocol grammar, proof body, q22 parameter, field, parser, verifier
acceptance rule, or security ledger was changed.  In particular, this result
does not establish global soundness, a 100-bit bound, an ordinary alpha
sampler law, extraction, or privacy.

## New Lean endpoints

| Leaf | Promoted declaration | Scope |
|---|---|---|
| `FSV8ProjectedFreshPositionalCut.lean` | `projected_fresh_trace_has_native_request_with_exact_cuts` | Generic projected-machine positional fresh cut with full entry/request/final history equalities. |
| `FSV8RootVerifierNativeRequestExactCuts.lean` | `returned_v8_verifier_query_has_global_native_request_with_exact_cuts` | V8 root lift for one returned verifier fresh query. |
| `FSV8AlphaCanonicalFreshCut.lean` | `fresh_cut_unique`, `fresh_cut_labels_equal` | Generic canonical ordinal facts; not a whole-root source bridge. |
| `FSV8AlphaExactRequestLabel.lean` | `scheduler_relation_alpha_label_of_exact_verifier_fresh_request` | Exact request-local alpha-label equality with cached history retained. |

The hypotheses in the new V8 root theorem are the returned functional
execution, a positional decomposition of its verifier `freshQueries`, and
the existing scheduler room hypothesis.  The semantic program, root-label
trace, source profile facts, target locality, and probability conclusion are
not hidden in the conclusion or supplied as coherence certificates.

## Checks

The supplied archive checksum manifest was verified before use.  Its
`python3 scripts/verify.py` run passed 44/44 finite/reference tests in 0.080
seconds; those tests are evidence for the supplied executable models, not Lean
proofs or a source refinement.

Focused Lean replay used the cached NUC Lean 4.32.0 toolchain through a
systemd user scope with `MemoryHigh=7500M`, `MemoryMax=8G`, and
`MemorySwapMax=0`:

| Target | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8ProjectedFreshPositionalCut.lean` | 0 | 2.69 s | 6,600,144 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8RootVerifierNativeRequestExactCuts.lean` | 0 | 2.89 s | 6,798,304 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8AlphaCanonicalFreshCut.lean` | 0 | 2.61 s | 6,724,464 KiB | 0 | standard foundations only |
| `FSV8AlphaExactRequestLabel.lean` | 0 | 2.50 s | 6,715,516 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |

The first attempted compile of `FSV8AlphaExactRequestLabel.lean` found a
missing import for `SchedulerNativeRequest`; the second found that `erase`
needed explicit unfolding.  Both were fixed locally.  No resource limit was
raised and the final focused run is the recorded one.  A search of the four
new leaves found no `sorry`, `admit`, custom `axiom`, or `native_decide`.

The supplied generic pack leaves had already been focused-compiled in the
same pinned toolchain; they were not rerun unchanged.  No full manifest or
package-wide replay was run.

The archive's executable reference checks can be rerun without touching the
worktree with:

```sh
cd /tmp/aspis-v8-alpha-causal.bWjNdu/aspis-v8-soundness-alpha-causal-pack-20260913
python3 scripts/verify.py
```

The Lean leaves require the repository's pinned 4.32 cache and were run as
individual `lean` targets, never as a cold package rebuild.

## Next decisive theorem

Construct a state-by-state refinement from `ExactRootFunctionalRun` trace
positions to the V7 operational history used by
`seekUnifiedExposure`.  It must preserve cached records and prove the same
input/state at the selected alpha request.  Only after that theorem can the
new exact-cut label equality be composed with
`FSV8AlignedAlphaHistorySlotBridge` and the existing router realization.
