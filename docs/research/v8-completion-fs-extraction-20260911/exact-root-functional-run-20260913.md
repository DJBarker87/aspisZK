# Exact V8 root success constructs the same-body functional execution

## Result

The promoted endpoint is
`FSV8AcceptedExactRootLiveExecution.returned_accepted_exact_root_constructs_live_execution`.
Starting from the executable exact-root scheduler result and its actual
`Runtime.accepted?` observation, it constructs:

1. the adversary prefix that returned the submitted body;
2. the verifier prefix that consumed that same dependent body;
3. the literal partition of one finite master answer tape between them;
4. the functional `wholeStagedScript` run from the adversary's actual final
   oracle projection;
5. equality of the functional result with the verifier-prefix result;
6. alignment of the two actual final oracle states; and
7. the previously proved live source/OOD/gamma/kappa/tau/alpha/query/rho and
   authenticated-suffix execution for the accepted record.

This closes the previously named deterministic scheduler-root-to-functional
success gap.  It does not prove a random-oracle probability law, restoration
collection, permitted-access payment extraction, global soundness or literal
Rust refinement.

## Why the bridge is success-local

The older forward compiler theorem required enough total-call, fresh-call and
tape room for the script's complete static call bound.  Those premises do not
follow from an actually successful shorter cache/retry path.

`FSV8SuccessfulProgrammedAlignment.returned_compileScript_aligned` instead
inducts through a machine run already known to return.  At every executed
query it obtains:

- the cached answer from the aligned table, or
- finite-tape availability from the actual successful controller answer.

Abort, fuel and resource failures are eliminated only by inversion of that
concrete returned run.  No capacity for unexecuted continuations is assumed.

The finite-tape controller is equated with the projected suffix controller
only on chronological extensions of the real boundary history, reusing
`FSV8FiniteTapeSchedulerSegment`; no false global controller equality is used.

## Focused evidence

Lean 4.32.0 at toolchain commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35` ran on the Tailscale NUC.  Each
leaf used one process under `MemoryHigh=8G`, `MemoryMax=9G`,
`MemorySwapMax=0`, `RuntimeMaxSec=600`, `-j1 -M8192`.  Existing pinned
dependency artifacts were reused; this was not a fresh transitive rebuild.

| Leaf | Exit | Wall | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| `FSV8ExactRootSuccessfulPrefixes.lean` | 0 | 2.56 s | 6,755,760 | 0 |
| `FSV8SuccessfulProgrammedAlignment.lean` | 0 | 2.53 s | 6,525,036 | 0 |
| `FSV8ExactRootFunctionalRun.lean` | 0 | 2.54 s | 6,724,512 | 0 |
| `FSV8AcceptedExactRootLiveExecution.lean` | 0 | 2.60 s | 6,722,436 | 0 |

Every promoted declaration reports only `propext`, `Classical.choice` and
`Quot.sound` (the tape-drop lemma needs only `propext`).  No `sorryAx` or
custom axiom occurs.

A separate hostile theorem-signature review classified all four leaves
GREEN for this deterministic scope.  It found no conclusion-shaped premise,
stale body/oracle/tape, dependent-cast substitution, return-as-acceptance
mistake, global controller-equality assumption or hidden static room premise.
The review identified the programmed-state alpha-cut-to-ROM event as the next
causal boundary; it did not promote this result to a probability theorem.

Machine-readable hashes and scope are recorded in
`results/v8-completion-fs-extraction-20260911/exact-root-functional-run-v1/report.json`.

## Remaining soundness boundary

This result supplies the deterministic execution consumed by the existing
local algebraic and authentication theorems.  The next coherent endpoint must
attach the exact accepted-execution classifier and permitted-access extractor
to this constructed run, then transport its explicitly partitioned failure
events through the adaptive random-oracle experiment.  Literal Rust/Aeneas
refinement remains outside this theorem, exactly as intended by the research
goal.
