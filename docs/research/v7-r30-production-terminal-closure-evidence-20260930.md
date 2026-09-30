# V7 R30 production observer to terminal relation closure

Predecessor `172cf74e3`, plus exact working-source hashes below. Remote pinned
Lean 4.32; individual systemd scopes used MemoryHigh=7G, MemoryMax=8G,
MemorySwapMax=0. Only one scope was active; all swaps were zero.

| Target | Exit | Wall s | Peak KiB | SHA256 |
| --- | --- | --- | --- | --- |
| V7ProductionSnapshotObserverR30TerminalClosure | 0 | 11.24 | 7240180 | 87a102619baebb8ec1f063330475baac839b6e04e0eb74f31c5de471e9a6bf8e |
| V7ProductionSnapshotObserverR30ProductionClosure | 0 | 4.60 | 7200752 | 3453c0da5479ab456d66e94203668a498a8f4f8b30e989982da60ab64af23f94 |

Both exported closure theorems print only `propext`, `Classical.choice`, and
`Quot.sound`.

`production_snapshot_observer_acceptance_reaches_terminal_closure` starts
with the literal successful production observer call. Its conclusion retains
the parser result, context conversions, hiding-context construction, source
layout-copy calls, accepted inner/circle/initial-fold/query-insertion/tail
witnesses, and the exact maintained three-round candidate-claim identity.
The layout equalities required by the established R26 theorem are derived
from the literal constant-copy callbacks. No external canonicality, running
claim, decoded-limb, or layout-equality premise is required at this boundary.

The terminal composition retains the copied sixteen-entry line component,
derives all canonicality premises, and applies the existing R26 source
terminal theorem. The new callback proofs follow post-decode source arithmetic;
they do not substitute the historical gamma-validation prefix or V8 research.

Scope: this closes the missing source-to-terminal **representation and terminal
relation** chain. It does not by itself establish a new cryptographic soundness
bound, Fiat--Shamir theorem, or exact mathematical gamma/fold polynomial identity
for the callback algorithms. Canonical-only callback theorems remain explicitly
canonical-only, and existing extraction/source-normalization boundaries remain.

Failed focused plumbing preflights: terminal exit 1 at
4.11s/7155628KiB and 7.49s/7168452KiB (dependent rewrite motives), then
10.97s/7188056KiB (default-instance bounded reads); production wrapper exit 1
at 4.30s/7150392KiB and 4.09s/7161952KiB (namespace and declaration plumbing).
The replacement proofs simplify named equalities and eliminate default values
only on proved bounded reads. No cap was raised and no resource failure occurred.

Consolidated focused audit: `V7ProductionSnapshotObserverR30ClosureAxioms`,
exit 0, 3.62s, peak 7140676KiB, swaps 0, source SHA256
`62079ace1cc45f6478291c533e88502693e41f9408d060202e4eb642ca235cf5`.
All eight audited boundary theorems have only the three permitted axioms.

Deterministic callback staging validated 142 Lean files with aggregate
`52993aea25dfa41d1e0f222726e5ed2da6f98b665b835708d19588edfd5d6465`.
The new separate R30 closure manifest checks all 336 transitive source modules
and the staging/replay tooling. The historical R26 manifest is left untouched.
Twelve external arithmetic/Aeneas/Mathlib imports use the pinned compiled cache;
this replay does not launch a cold dependency build.

Final frozen manifest replay is the remaining verification step.
