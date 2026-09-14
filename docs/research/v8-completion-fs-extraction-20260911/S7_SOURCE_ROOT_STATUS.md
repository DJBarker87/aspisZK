# S7 dependent-root milestone

Base revision: `9f161d6ba1c34adb93ab8ed0b95d26c1fac95db3`.

This continuation closes the old **caller-supplied semantic context** defect
for a guard-relaxed functional root. It does not close the S7 packet's global
soundness objective.

## Constructed now

`FSV8S7DynamicSelectedRoot` runs one bounded adversary from the empty lazy
oracle, consumes the exact body it returns, and continues on the same oracle.
The verifier parses that body once, executes the semantic transcript, and uses
the resulting `z` and digest in the selected suffix. The two operational Merkle
roots also come from that same parse. `DynamicConfiguration` contains no
caller-supplied `z`, digest, `RootCuts`, or profile Boolean. Its selected root
fixes the completion track's positive-transfer research profile.

The runtime result is dependent on the adversary's body, and
`run_dynamic_root_trace_is_erased_exposure_trace` identifies the trace of the
result-carrying root with the exposure trace used by the probability model.
This removes the unsafe option of selecting the semantic context after seeing
the random tape.

`FSV8S7SelectedSourcePrefixBudget` separately composes the same-body semantic
rounds, the 87-field point absorb, the read-only OOD/source prefix, response0,
nonce marker, and alpha0 sampler. It proves conservative syntax bounds of:

- 3,195 calls/fresh slots through response0;
- 3,262 calls/fresh slots through alpha0.

These bounds have no `priorSourceBound`, `workBudgetBound`, or
`adversaryFuelBound` premise. They apply to success, rejection, cache hits, and
sampler exhaustion in this guard-relaxed model. The sharper proposed 420 bound
is not proved: the current `Script` index charges the full 66-call capacity for
each ordinary QM31 sampler and needs a new path-sensitive cost proof.

`FSV8S7CompactWordTargetInclusion` closes one algebraic source seam. Given the
concrete word/covector chunks, a member of the concrete reference family, a
false word-dot claim, and an actual compact-polynomial collision, the sampled
alpha is in `CompactTargetData.target`. The false claim eliminates the zero
polynomial branch; target cardinality remains the already checked degree-six
family bound.

## Scope that remains open

The dynamic root is deliberately guard-relaxed. `FSLiveSemanticPrefix` does
not execute the selected payment terminal, so the new accepted value is not
literal Rust acceptance. The `RootCuts` fields used only for chronological
authentication analysis are inert; only the roots consumed operationally by
the suffix are body-derived. No authentication chronology is claimed from
those inert fields.

Therefore the actual-root ordinary bad-event theorem is still open. Its next
source theorem must construct, from one successful literal execution:

1. the selected terminal-success-to-relaxed-run inclusion and effect equality;
2. real chronological C1/C2 cuts and authenticated prefixes;
3. concrete compact chunks, reference-family membership, false-claim or
   identity disposition, collision, and routed decoder success;
4. target availability at the original creator for cached alpha outputs.

The existing fixed-configuration routed probability theorem cannot be applied
to the new dynamic root by choosing a configuration after the tape. A new
dynamic-root routing theorem or a direct source-to-killed-kernel pushforward is
required.

Operational extraction also remains open. The exact dependency map is in
`s7-extraction-blockers.json`. In particular, the staged root does not execute
the compact relation terminal and therefore cannot yet produce the 116
`RecoveredMiddleFork` records, collector progress, selected semantic
residuals, or literal `extract_checked` success.

## Validation

All Lean compilation was run on the Tailscale NUC with Lean 4.32.0, one
focused target at a time, under `MemoryHigh=8G`, `MemoryMax=9G`,
`MemorySwapMax=0`, and `RuntimeMaxSec=600`.

| Target | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `FSV8S7DynamicSelectedRoot.lean` (final renamed endpoint) | 0 | 12.87 s | 6,760,380 KiB | 0 |
| `FSV8S7SelectedSourcePrefixBudget.lean` | 0 | 2.93 s | 6,811,964 KiB | 0 |
| `FSV8S7CompactWordTargetInclusion.lean` | 0 | 2.95 s | 6,579,760 KiB | 0 |
| `FSV8S7DynamicSuccessfulCut.lean` | 0 | 2.95 s | 6,770,908 KiB | 0 |
| `FSV8S7Audit.lean` | 0 | 2.76 s | 6,737,912 KiB | 0 |

The promoted declarations report only `propext`, `Classical.choice`, and
`Quot.sound`. No retained S7 Lean source contains `sorry` or a new axiom. The
S7 packet's read-only checkout preflight passed at the base revision, and its
Python reference suites passed 37 and 15 tests respectively. These tests do
not prove source refinement or probability composition.

One first dependent-cut replay resolved an older root-level OLean before the
new module and failed on the renamed type. The final replay places the current
source directory first in `LEAN_PATH`, rebuilds the dependency there, and
passes. This is recorded as a cache/search-path provenance issue, not a proof
failure or a reason to trust the stale artifact.

## Closure decision

The proof body and verifier protocol are unchanged; the maximum remains
40,282 bytes. No Rust, SBF, production acceptance, deployment, or CU result was
changed or rerun.

The S7 packet is **not globally green**. Wave A is green only for the
guard-relaxed dependent root; Wave B is green for the conservative functional
bound; the compact target inclusion sublemma is green. Waves C--F remain
blocked by named source producers rather than arithmetic compilation.

The decisive next experiment is to model and differentially trace the literal
selected semantic terminal on the constructed `FSLiveSemanticTerminalInput`,
then prove successful literal execution follows the same relaxed continuation
and supplies real chronological C1/C2 cuts. That is the shortest route from
this milestone to an actual-root ordinary-event inclusion.
