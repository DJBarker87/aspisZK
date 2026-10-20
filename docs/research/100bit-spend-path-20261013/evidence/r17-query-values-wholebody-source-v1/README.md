# R17 QueryValues whole-body source bridge

This packet records two focused Lean targets that connect the mechanically checked raw Aeneas `verifier.query_values_entry` body to the accepted stored-coordinate theorem.

`R17QueryValuesWholeBodyV21` keeps the emitted function body and its branch/error propagation structure intact. Only the enumerated operation/callee names and the error callback are parameterized. `sources/check-source.py` reconstructs the raw body from `GeneratedFuns-v1.lean` and checks byte-for-byte equality after those explicit substitutions. The raw generated function body is 2,381 bytes and its substituted body hash is recorded in the source checker output in `receipts/v34/lean.log`.

`R17QueryValuesWholeBodyStoredV1` fills the callee record with the accepted current CM31 and M31 operation records, current `fibre_point` and `line_node`, and the concrete M31 one constant. It proves equality with `R17QueryValuesEntryActualV1.queryValuesEntry`; then it transports raw-body success to the existing `successful_queryValuesEntry_stored` theorem. There is no separate adapter-success assumption. The iterator `anyCheck` remains a parameter, so this packet does not prove its callback is the concrete zero test.

Both targets exited 0 and printed only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. Lean 4.32.0 was used. Receipts report both process RSS and cgroup scope memory: v34 process peak 3,897,064 KiB and cgroup peak 369,467,392 bytes; stored-v6 process peak 3,886,816 KiB and cgroup peak 364,605,440 bytes. Swap was zero in both scopes. Limits were MemoryHigh 1 GiB, MemoryMax 2 GiB, MemorySwapMax 0. These are different measurements; the process RSS figure is not the cgroup peak.

The source, checker, receipt, preflight, command, Lean log, timing log, config, and included dependency source snapshots are retained here. The target's full ordered LEAN_PATH and direct-import hashes are in each preflight/config. Build objects are intentionally omitted. The Rust `Iter.any` callback implementation is outside this packet and remains an explicit boundary.

The publication also includes the previously unpublished v34 propagation dependency and its successful receipt. The canonical manifest records all three module identities and their exact selected object hashes; the older v22 dependency is not substituted for v34. The standard-only axiom audits and direct dependency source owners were checked without recompiling unchanged targets.
