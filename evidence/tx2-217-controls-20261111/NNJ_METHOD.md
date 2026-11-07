# Exact scope and fidelity method

This job supplies only ruling(t) native contract calibration for TX2:217. It changes no RowSpec, emitted definition, caller clause, runtime trust, native multiplication stub or cryptographic premise. The ledger alone decides credit. NMX's original fidelity harness/function names are retained; new assignment module is NNJ_assignment. Original decoder and assignment native bodies remain unchanged (assignment source-cut equality is independently checked by NNJ_validate.py).

Two interface shapes:

| Shape | Contract law used for calibration | Unimplied assertion |
|---|---|---|
| Result<Box<PoolV1PairForestLaneStateV1>,ProgramError> | NMX_shape returns Err, ensures only is_err | exact InvalidAccountData tag; another typed error satisfies is_err |
| Result<(),ProgramError>, &mut [M31;8] | NMX_assign_post describes result and one selected digest cell; modifies whole node | with zero window, real body writes all zero cells; the contract constrains only selected cell, leaving the other cell arbitrary |

The decoder inverted-ensures gate is the original NMX_K006 shape at the actual wrong-length decoder, rerun NNJ_K005 with inverse env. Its Result carrier is identical. Empty-modifies controls write an actual mutable argument and must fail an assignability check. Assignment NNJ_K010 changes only the modifies annotation via cfg nnj_empty_modifies; its actual body and postcondition are unchanged. The proof_for_contract and caller builds preserve body bytes, with exact source hashes. All source variants and env/feature lists are retained by attempt.

Typed constructors are implemented only in the type's defining crate, avoiding orphan-trait violations. Private CARGO_HOME makes an isolated registry copy of solana-program-error2.2.2; both index-name copies are instrumented identically. Shared cache/index are read-only symlink inputs, never source-mutated. All shared original lib.rs hashes are checked before every run. ProgramError has26 variants, unrestricted Custom(u32), and a≤1-byte BorshIoError payload. This bound is a calibration underapproximation, not a domain restriction on any shipped caller or a universal full-String havoc result. A payload-free InvalidArgument is an explicit legal witness satisfying is_err but violating the decoder's exact-tag assertion; no concrete solver trace of that particular tag is asserted. Lane fields are unrestricted, including every u32 M31 representation; Box uses Kani's existing typed allocation support.

The NMD two-build annotation-free pattern is needed for a naked constructor kani::stub replacing an annotated function (K126), not for a kani::stub_verified using its generated contract. NNJ uses the latter and preserves identical callee bodies across positive and caller builds. It does not claim the NMD minimal ProgramResult constructor method establishes a full native parent or SDK footprint.

KMX: exact patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67, exact original KMX_stubs.rs, and original hooks in NMX assignment. No new copy stub. Copy fidelity controls use original KMX_checks names in the SAME program/deployed feature configuration, graph and frozen lock. No field product, SHA implementation, long buffer or whole-parent native harness is evaluated.

No Option/function-pointer-dependent or writable-static property is used. The unused observer-bearing production functions in the compilation are not evidence roots. No output depends on such a value. Reused native semantic-transport trust remains an existing P6/D188 option-A reclassification, not an additional trust item or removal.

No new Lean declarations: raw ax2 and print axioms have empty new-root inventories; NNJ_COMBINED_IMPORT.lean records ledger25 import only, uncompiled under the controls-only instruction. No unchanged import/audit or frozen-manifest replay. Ledger26 already replayed the candidate's Lean closure and named the sole control gaps. No Lean cache is copied or modified by NNJ.
