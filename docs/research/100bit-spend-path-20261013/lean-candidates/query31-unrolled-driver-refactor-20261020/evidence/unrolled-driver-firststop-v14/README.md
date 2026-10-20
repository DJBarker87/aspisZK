# Query31 unrolled driver first-stop proof (v14)

This source/evidence packet is a candidate-only Lean check. It does not modify
production and does not establish equivalence to the original iterator-based
Rust implementation.

The proof imports only the checked `AspisR1Query31Transcript.Types` owner. It
does not import generated `Funs` or `FunsExternal`. The local declarations
`QUERY_COUNT`, `QUERY_MAX_DRAWS`, and `QueryScan.finish` are exact copies of the
normalized generated Funs source; `check_source_adapters.py` verifies their
source bytes along with the generated driver body. The generated driver body is
copied exactly except that its initial default state is an explicit `scan0` and
each scan operation is an explicit `scanFn` boundary.

The concrete finish behavior is retained in `finishAdvance` and proved by
`finishAdvance_success` and `finish_success_iff`. The theorem
`successful_driver_has_trace` inverts success of the full adapted eight-branch
driver to one first-stop trace. For indices 0–6 it records false scans before
the selected true scan. If all seven are false, index 7 is scanned and its
boolean is ignored exactly as in the source; the result uses `advances[7]`.
Each case also retains successful concrete finish and the selected advance
lookup. There are no independent scan-success or finish-success premises in
this inversion theorem.

The remaining explicit operation boundary is `scanFn`, with the initial state
`scan0`. The earlier scanner proofs use a nominally different generated
`QueryScan` type, though its record has the same fields and field types. This
packet does not yet prove the structural state adapter or scanner operation
correspondence. Original iterator-driver equivalence therefore remains open.

The transitive `Types` owner includes the generated external *type* declarations
needed by the data types. The generated external *function* owner is absent
from this import closure. Axiom audits for `finishAdvance_success`,
`finish_success_iff`, and `successful_driver_has_trace` each report only
`[propext, Classical.choice, Quot.sound]`.

## Focused receipt

Target: `Query31UnrolledDriverFirstStop`; source SHA
`ea5c3cb0449e09d7c12f8b98adf7fbc2be19137ca4f64f6122bc879689a7597b`; object
SHA `3f55aa6565f01c860024451ba2a7b3bf9b76b2f3ef9d866b723d3d3f37c88b86`.
Lean 4.32.0 SHA: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The NUC scope exited 0 in 1.706 s, peak process RSS 2,585,000 KiB, cgroup
peak 316,825,600 bytes, swap 0; MemoryHigh 1 GiB, MemoryMax 2 GiB,
MemorySwapMax 0. The exact preflight, command, time log, Lean log, admission,
and reservation are included. The Lean log contains one no-op `change` linter
warning; all targets compiled and the axioms listed above were printed.

No `.olean` or executable artifact is included. v14 supersedes v12/v13, whose
proof sources imported generated Funs or did not match the staged source bytes.
