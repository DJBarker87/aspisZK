# R17 query-values source-cut proof packet

This packet records the focused Lean proof of the successful `verifier.query_values_entry` result chain and its composition with the accepted `R17QueryPerItemValuesV2.successful_perQueryCore_stored` theorem. It is a source-cut consumer packet, not a whole `QueryGeometry::for_range` refinement.

The generated `Funs.lean` is pinned at SHA-256 `7719ef4e98cbfe031d0bbcdc3b3bc9f320dd455752f728a130333d5f24084533`; the emitted function is documented at `lib.rs` lines 381:0–391:1. The accepted v22 proof source is `sources/R17QueryValuesEntryActualDefs-v22.lean`, SHA-256 `cc6f20c465a77bac9a083d319b2e9f8b1950ab85554ef2c50ef772e117b750d7`. The v22 receipt and full Lean log are under `evidence/v22/`.

The green theorem `successful_queryValuesEntry_stored` derives from success of the adapted helper: the query index is in range; the two checked line indices equal `u / 4 * 4` and `u / 4 * 4 + 3`; the source-ordered fibre and line operations and subsequent z calculation all succeeded; the returned five-element array has the emitted order; and decoded outputs match the stored initial circle point, stored first-line values, and `2*x^2-1`. It also exposes the successful `anyCheck` result as `false`.

The Lean source preserves the helper’s call order and checked operations. It abstracts the `Error` payload to a local two-constructor type, parameterizes the `Slice.iter.any` call, and expresses the emitted `map_err`/`Try::branch`/`FromResidual` propagation as direct matches. `sourceMapTryFromResidual_eq_directMatch` proves the propagation rewrite by cases, including callback `ok`, `fail`, and `div`; the error-mapping closure theorem pins the resulting `Query` error. The checker verifies the raw generated function bytes, ordered clauses, and presence of the propagation proof. It does not establish full generated-body identity or equivalence of the explicit M31/CM31 operation arguments to the generated fast-domain bodies.

The iterator callback remains an explicit premise: this packet does not prove that the concrete `SliceIter.any` implementation visits every array element or that its equality callback is equivalent to field zero. The entire enclosing `QueryGeometry::for_range` Vec loop and its connection to the eight-block caller also remain open. No external-template axioms are imported by the adapted source. The v22 axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`; the direct propagation equation uses `propext` and `Quot.sound`.

## Evidence

- v19 is the green predecessor that established actual helper success inversion, checked-index formulas, array order, and successful false callback. See `evidence/v19/`.
- v20 and v21 are failed theorem-source repairs (unbound dependent witness names and then an unqualified `decoded` constant); their logs are retained under `evidence/v20-failed/` and `evidence/v21-failed/`.
- v22 is the accepted corrected theorem and stored-coordinate composition. It ran Lean 4.32 with the staged direct imports pinned in `evidence/v22/preflight.json`, under MemoryHigh 1 GiB, MemoryMax 2 GiB, MemorySwapMax 0. Its receipt records exit 0, 2.107 seconds, scope peak 383,950,848 bytes, and zero swap.
- The direct dependency source and receipt records for `R17QueryPerItemValuesV2` and `R17QueryIndexArithmeticV6` are included under `dependencies/` and `evidence/deps-*`.

Run `./check-source.py` to verify the local source pins and ordered-clause scan. The checker deliberately reports its limited scope in `source-check.json`.

Publication status: PROVED adapter semantics and checked index/stored-coordinate composition; CANDIDATE source cut. The formal map/Try propagation lemmas are checked, but their whole-body application to the pinned generated helper has not yet been proved. This packet does not close source correspondence or the concrete any implementation boundary.
