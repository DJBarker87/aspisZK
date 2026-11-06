# Native cuts

All cuts use local mutable logs, the exact KMX patch (bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67), frozen-lock validation before every run, offline dependency resolution and unchanged post-run lock. No writable static, function-pointer assertion, function contract, new copy stub or field multiplication is used.

TX1:321: NKG_columns_iteration outlines exactly ONE frozen loop body on arbitrary weights, all three arbitrary columns, arbitrary output and lane<16. It logs all six arguments of each of four scalar interpolation calls, uses unconstrained complete replies and asserts lane+1, call count, SAME arguments, exact selected write and every disjoint output cell. K001 PASS; K002 output corruption and K003 argument corruption FAIL. K004/K005 rerun exact KMX pointer-copy calibration, PASS/FAIL. K006/K007 exit frame at lane>=16 PASS/FAIL; K008/K009 source ZERO initialization PASS/FAIL. No canonicality assumption in these native cuts, hence none stronger than the caller.

The source-erasure checker rejects a changed constant-column argument. Hashes and complete scratch patches are retained per attempt; source/harness association is P6/D188 option-A reviewed transcription, reclassification, not removal. These native cuts alone do not establish the row.

TX1:324: NKG_internal_calls is prepared, not yet verified. It outlines the frozen full body with local-record logging oracles for both dot calls and both internal rounds; complete argument and return arrays, SAME selector/constants and source ordering are asserted. No arithmetic value is claimed from unconstrained replies.
