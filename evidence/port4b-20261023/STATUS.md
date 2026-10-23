# P-B batch port

Branch codex/cx-port4b-20261023; starting revision
986dc0bd7daf04ecd14cd0459585855277fef937. S2 OPEN.

Read the security/proof discipline, shared/local Lean rules, S2 ownership,
lead plan/diagnosis, route-B ruling, lead interface, PORTS3 row table and
VERIFIER-TOP. Paths without a root are under
`docs/research/100bit-spend-path-20261013/`; PORTS3 is at root design/.

Stage 1: inspected current batch Rust and installed emitted parent. The
emitted loop's nonzero-padding, excessive-count and verify-false paths return
`done (..., none)`; its wrapper maps none to Aeneas panic. Actual Rust returns
Parse or Merkle. This is a candidate error-lowering obstruction to exact
full-Result transport, not a shipped vulnerability and not a refutation of
an accepted-run-only port. Next isolate the error path in a small checked
module and retain the independent S2CallerFacts node-view/P6 construction.

No shipped changes; no ELF trigger. Inherited pins default f8c0ec72…,
devnet 63ad3e9c…, Pool 121f3e29… are not newly reproduced. No keys touched.
Host launcher has private Port4B objects, global lock (night window elapsed),
6G/8G/Swap0/Tasks64, 180-second timeout and aggregate reservation admission.
Budgets at stage 1: Lean 0/100; Kani 0/60. No release replay.

Stage 2: `Port4B_Rejection` proves that the two local padding-return
carriers differ and their shared emitted decoder gives panic versus Rust
Parse. `source-audit.json` pins the exact corresponding branches in current
Rust and emitted source. This is a local branch obstruction, not a proved
reachable complete native counterexample. Corrected full-error port requires
repair/re-extraction of those branches; accepted-only transport must separately
prove native child/effect/argument correspondence and retain rejected-query
prefixes in the surrounding security experiment. P6 sourceBatch returns Bool
and cannot retain the Parse/Merkle distinction without an additional carrier.

Attempt001 is EXCLUDED: an overlarge whole-parent normalization hit a kernel
memory ceiling after elaboration failed (exit1,11.684145461s,4507840KiB,
swap0). No cap was raised and it was not rerun unchanged. Replacement002
isolates only the pending-return branch: exit0,3.342520367s,4413180KiB,
swap0; all three theorem audits standard axioms. This does not give proof
credit to the failed whole-parent theorem or its recovery axiom.

Budget after stage 2: Lean2/100, Kani0/60. Exact targets, source revisions,
source/dependency hashes, limits, full errors and axioms are in lean-*/.
