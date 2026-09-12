# Actual alpha scheduler and configuration coherence

Status: focused deterministic Fiat--Shamir/source-integration milestone. This
is not a probability theorem, matrix-completion theorem, or global soundness
result.

## What changed

`FSV8ReplayConfigurationExactness.lean` proves that a replay configuration is
the canonical gamma or alpha boundary configuration, when all six replay
controls are inherited from that configuration, exactly when its
`transcriptDrivingInput` equals the corresponding replay-derived candidate
input. The proof introduces no coherence assumption. It reduces the remaining
producer obligation from equality of a seven-field structure to one literal
byte-string equality.

`SuccessfulReplayAlphaConfigurationDisposition.lean` uses that reduction to
give every successful replay and arbitrary selected configuration a total
classification:

1. it is exactly the boundary configuration constructed from that replay and
   retains the existing prior-adversary / prior-table / absent target
   disposition; or
2. its driving input is literally different from the replay-derived alpha
   request.

`ExtractionCollectorActualAlphaConfigurationFamily.lean` carries this total
classifier pointwise across the existing 29 by 4 verified-successful replay
family. It does not infer alignment from `CompleteMatrix`, labels or list
membership.

`SuccessfulReplayActualAlphaSchedulerScan.lean` searches the existing
result-carrying scheduler for the replay-derived alpha input. The executable
scan is total. A paused result exposes that exact fresh request and reconstructs
the original run with the actual retained answer and suffix. An absent result
is proved equal to the original scheduler run. Cached requests are not called
fresh pauses.

`ExtractionCollectorOperationalSuccessfulReplay.lean` retains the exact
`CoupledReplay` and `constructLegalReplay` equality used to construct the
same-body `SuccessfulReplay`. It also retains equality of the projected oracle
and the successful halt of the compiled `wholeStagedScript`; these facts are no
longer lost behind an existential successful replay.

`ExtractionCollectorOperationalAlphaScheduler.lean` then replaces the arbitrary
cursor and answer-list inputs with source-shaped values for one checked cell. It constructs the cursor
from the replay's literal V7 oracle, the compiled V8 script, verifier actor,
limits and fuel, and supplies the same finite tape dropped at the state's
fresh-call count. It also carries the separately proved successful machine
halt. The missing scheduler/controller refinement means the scan is not yet
proved equal to that successful machine execution.

That segment begins *after* the restoration replay has installed the
programmed entry. Accordingly, the alpha request may be a cached call that the
fresh-request scanner normalizes and reports through its absent branch. This
leaf does not replace the required global cursor beginning before the atomic
fork. Rather, it fixes the exact post-programming endpoint that the global
fork continuation must reach.

## Security implication

The previous hidden seam is now an explicit event rather than a supplied
coherence premise: every selected cell is either aligned with its actual alpha
boundary or has a concrete input mismatch. Separately, once a chronological
scheduler cursor is constructed, fresh occurrence versus absence is an exact
operational split at that actual input.

This still does not bound mismatch, absence or prior-table mass. The decisive
next producer must construct the V8 root scheduler cursor and master answer
tape from the same source execution, then nest the gamma and alpha pauses. It
must retain cached/prior targets, scheduler failures and resource aborts. Equal
decoded field values are not enough to discharge the byte-input equality.

The deterministic nonzero-sampler bridge is also incomplete: existing V8
four-block decoding agrees with the V7 raw decoder, but no theorem yet packages
the actual adaptive transcript blocks and residual state into the V7 successful
retry sample space. Consequently the V7 uniform-PMF bounds are not yet
applicable to this V8 execution.

## Focused checks

All successful commands used Lean 4.32.0, `-j1`, `-M7500`, the pinned union
cache, and the repository `AspisFormal` search path. No full manifest was run.

| Leaf | Exit | Wall | Maximum RSS from `/usr/bin/time -l` | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8ReplayConfigurationExactness.lean` | 0 | 8.62 s | 5,593,579,520 B | 0 | none |
| `SuccessfulReplayActualAlphaSchedulerScan.lean` | 0 | 5.22 s | 5,722,095,616 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `SuccessfulReplayAlphaDisposition.lean` dependency artifact | 0 | 18.58 s | 5,754,273,792 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `SuccessfulReplayAlphaConfigurationDisposition.lean` | 0 | 4.20 s | 5,771,182,080 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `ExtractionCollectorActualAlphaFamily.lean` dependency artifact | 0 | 3.93 s | 5,791,006,720 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `ExtractionCollectorActualAlphaConfigurationFamily.lean` | 0 | 5.19 s | 5,782,519,808 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `ExtractionCollectorOperationalSuccessfulReplay.lean` | 0 | 13.40 s | 5,714,378,752 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `ExtractionCollectorOperationalAlphaScheduler.lean` | 0 | 15.01 s | 5,756,272,640 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |

The macOS tool separately reported peak-memory-footprint values around 870--885
MiB; raw command output used both metrics. No swap was reported.

Two early scheduler-leaf attempts failed before theorem checking because the
required namespaces for `Script`, `Digest256` and
`runSchedulerNativeListRun` were not open. A third failed in the branch proof
because the generalized scan equation was used where the substituted goal was
reflexive. The retained source opens the exact namespaces and uses reflexivity
only for the substituted existential equality while retaining the original
scan equation for the reconstruction theorem. No unchanged failed command was
rerun.

Evidence directory:
`results/v8-completion-fs-extraction-20260911/actual-alpha-scheduler-coherence-v1/`.

Global soundness bits remain unset. Grinding contributes zero bits.

## Hostile statement review

A separate agent inspected all four retained theorem signatures and unfolded
their critical constructors before reading this completion note. It found no
conclusion-shaped premise, post-challenge target freeze, vacuity, or claim of
probability/chronology beyond the premises. It specifically confirmed that
the scheduler cursor and answer list remain arbitrary inputs to the scan
theorem, `CompleteMatrix` and resource/projection facts remain visible in the
family theorem, and the mismatched configuration branch is not silently
discarded. That review is source-level peer review, not independent kernel or
cryptographic validation.

A second hostile review covered the operational replay and source-shaped
scheduler leaves. It confirmed that the replay, body, accepted result,
projected oracle and finite-tape machine halt are constructed rather than
assumed. It also caught the important remaining interface: `machineExact` is
carried but not consumed by the scheduler scan proof, so the dropped tape list
is not yet proved to drive the same successful execution. The source comments
and gate ledger were narrowed accordingly.
