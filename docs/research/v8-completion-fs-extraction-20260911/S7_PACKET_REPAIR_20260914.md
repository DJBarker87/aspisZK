# S7 packet repair: terminal input and pre-alpha ordinary cut

This is a scoped repair of the S7 literal-root packet.  It intentionally does
not claim a global soundness result.

## Repaired checked leaves

`SelectedPositiveTerminalDeltaSource.lean` constructs the selected opt-in
positive-transfer terminal correction from one canonical parsed body and the
live semantic result.  It fixes the source row-1014 selector, residual claim
slots 272/301/274, the `theta^27` lane-94 contribution, equality/eta factors,
and the final wrapper addition.  It has no terminal callback, terminal-success
or witness premise.  The surrounding pair-forest masked terminal remains a
separate literal-source evaluator/refinement obligation.

`FSV8S7PreAlphaConcreteOrdinaryCut.lean` constructs a pre-alpha cut from a
successful run of the selected guard-relaxed source prefix.  The canonical
body/wire, dynamically produced `z`, OOD state, gamma, kappa, tau,
`fromInputs` functional claim, canonical response0 and compact relation
coefficients are all produced by that execution.  This removes those values
from the old caller-supplied ordinary configuration.

The exact consumer `cut_false_claim_collision_mem_target` still takes the
received-word/covector chunks, finite reference family, false discrepancy and
compact collision explicitly.  That is deliberate: the prefix result does not
yet contain an authenticated virtual quotient/covector construction or a
theorem that an actual ordinary discrepancy produces the collision.  Moving
those inputs into `Cut` would recreate the caller-supplied target defect.

## Rejected cut shortcut

An attempted C1/C2 trace-factorisation was removed rather than retained
uncompiled.  The existing semantic Script returns only its final semantic
state.  Real chronological cuts need a run-level continuation-factorisation
lemma for the padded `Script.bind` interpreter, followed by inversion of the
three execution segments.  A syntactic refactor is not definitionally equal
because the continuation padding differs.  No inert `RootCuts` value is
promoted as an authentication cut.

## Checks

The packet preflight against the current descendant reported all selected
baseline blobs unchanged.  The supplied reference suites passed:

- `tests/test_source_reference.py`: 37 tests;
- `tests/test_utilities.py`: 15 tests.

Focused Lean checks ran on the Tailscale NUC, pinned Lean 4.32.0, one leaf per
systemd user scope with `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0` and
`RuntimeMaxSec=600`:

| Leaf | Result | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `SelectedPositiveTerminalDeltaSource.lean` | exit 0 | 4.03 s | 6.6 GiB | 0 |
| `FSV8S7PreAlphaConcreteOrdinaryCut.lean` | exit 0 | 13.92 s | 6.6 GiB | 0 |

Both promoted leaves print only `propext`, `Classical.choice` and
`Quot.sound`; no retained new Lean source uses `sorry` or a new axiom.  The
S7 focused runner now includes both leaves.

## What this does not close

This repair does not prove literal Rust-to-model refinement, real C1/C2
authentication chronology, source ordinary-event inclusion, the fresh/cached
ROM router, permitted-access extraction, payment validation, full-view ZK, or
global probability composition.  Therefore it supports no global 100-bit
claim.  The immediate next proof is the run-level semantic continuation
factorisation that exposes actual C1/C2 cuts, followed by an authenticated
virtual-word/covector producer at the pre-alpha cut.
