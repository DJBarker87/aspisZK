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
