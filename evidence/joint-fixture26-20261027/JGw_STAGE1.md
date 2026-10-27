# Native tree adapters

Checked JGw_Tree0/1/2.tree on the actual retained proof and queries, all roots,
and the shared returned scratch arrays. Tree0 imports JGu_Terminal0.loop;
terminal1/2 reuse all JGu child certificates. The outer lo/hi monadic pair
is rewritten by a named equality, followed by an explicit monadic change.
The wrapping slot for trees1/2 is rewritten explicitly.

Attempts 001..006: five pass, 003 failed definitional equality of the wrapping
slot. 004 replaces it with an explicit wrapping slot expression and theorem.
No timeout/memory kill. All successful new roots print only the standard
propext/Classical.choice/Quot.sound axioms. Exact targets, source hashes,
revision, dependencies, wall/RSS/swap/limits and full diagnostics are in each
receipt directory. Failed recovery axioms have no credit.

No FJv top premise removed; accepted1 and joint non-vacuity remain open.
No shipped files or artifacts changed. 6/100 Lean launch attempts, 0/10 Kani.
