# Fixed-array8 contract fidelity

Additional strict ruling(t) calibration requested after the primary gate. No new Lean module, stub_verified production composition, trust row or source-body change is introduced. Native harnesses live only in the owned scratch tree and are retained in NJT_Q_array8_calibration.rs.txt / NJT_Q_NATIVE.patch.

The array8 calibration contract promises only first-cell correctness and pure modifies(). The real-body caller asserts second-cell correctness, which is deliberately not implied by that contract; the identical caller harness under stub_verified must fail that assertion. Contract and caller names remain unchanged between positive/control configurations. The modifies pair returns the same fixed-array8 carrier and uses an ordinary local mutable record: only its allowed field is declared writable, and the negative configuration also changes its framed field.

All gates retain exact KMX, frozen offline dependency/feature validation and unchanged-lock checks. All controls have their expected verdicts below. QK005 additionally retains the actual068 inverted-ensures failure. Authoritative source/feature/lock/receipt pins are NJT_QSHAPE_FIDELITY.json; every scope preserves the fixed90s harness limit.

| Attempt | Expected and actual | Purpose | Wall seconds |
|---|---|---|---|
|NJT_QK006|PASS|weak first-cell contract positive|76.596|
|NJT_QK007|FAIL as intended|same contract inverted ensures|66.778|
|NJT_QK008|PASS|unimplied second-cell assertion on real body|5.792|
|NJT_QK009|FAIL as intended|SAME caller under stub_verified|2.785|
|NJT_QK010|PASS|local-record allowed-field modifies positive|69.705|
|NJT_QK011|FAIL as intended|SAME local-record contract with undeclared frame-field mutation|64.378|

QK007 fails the inverted first-cell ensures; QK009 fails precisely the unimplied second-cell assertion; QK011 fails precisely `Check that *var_4 is assignable` for the undeclared framed field. Positive/modification controls use local records only. No writable static, Option<fn>/function-pointer-dependent property, suspended/quarantined harness, timeout, memory kill, shape repair or renaming occurred. The only stub_verified use is the deliberately failing fidelity fixture; no production composition changes.

QL033 checks all expected verdicts and source hashes, archives complete metadata and every crate feature list, verifies both retained Lean exports and frozen lock unchanged, then removes only this job's recreated target/temp outputs. No Lean module or compiled object changed; primary combined/NFX/raw gates need no rerun.
