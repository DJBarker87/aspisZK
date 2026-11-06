# NKG native cuts

All accepted cuts have the exact same archived complete harness source as their matched failing controls. `NKG_NATIVE_PINS.json` and the per-attempt `NKG_INPUTS.json` bind it. Every run independently validates the frozen resolved dependency graph and deployed crate features, uses CARGO_NET_OFFLINE=true, and verifies Cargo.lock unchanged. All copy-dependent runs use exactly KMX_copy_stubs.patch SHA256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`; K004/K005 calibrate its pointer-copy positive/negative configuration. No new copy stub, writable static, function-pointer verdict, function contract or stub_verified is used.

| Frozen source segment | Positive | Failing controls | Lean transcription/composition |
|---|---|---|---|
| 321 one arbitrary lane, all scalar arguments/replies and disjoint frame | K001 | K002 output, K003 arguments | ColumnCuts.Step, ColumnLoop, ColumnsPacket |
| KMX copy window | K004 | K005 | existing KMX value laws |
| 321 loop stop | K006 | K007 | ColumnCuts.Trace |
| 321 ZERO initialization | K008 | K009 | ColumnCuts.Trace |
| 324 complete dot/round forwarding | K013 | K011 output, K012 arguments | HelperCuts.Internal, InternalPacket |
| 323 complete columns/full-round forwarding | K014 | K015 output, K016 arguments | HelperCuts.Full, FullPacket |
| 308 one arbitrary low-fold iteration | K017 | K018 output, K019 arguments | OracleCuts.Low, LowFrame finite induction |
| 308 prepared constructor raw nine-word replies | K032 | K033 output, K034 arguments | PreparedRaw, OracleCuts.Prepare |
| 308 four-element final constructor | K026 | K027 output, K028 index | OracleCuts.Output, BuilderRaw |
| 308 child branch prefix | K029 | K030 output, K031 arguments | OracleCuts.Prefix, PreludeFrame |
| 308 pack segment at arbitrary group | K035 | K036 output, K037 arguments | OracleCuts.Pack, GroupFrame |
| 308 three differences | K038 | K039 output, K040 arguments | OracleCuts.Sub, GroupFrame |
| 308 prepared sum | K041 | K042 output, K043 arguments | OracleCuts.Sum, GroupFrame |
| 308 prepared block multiply forwarding | K044 | K045 output, K046 arguments | OracleCuts.Mul, GroupFrame |
| Raw nine-word factory/accessor calibration | K047 | K048 | PreparedRaw extensional carrier |
| 308 direct leading selector read | K049 | K050 | PreludeFrame.Cut |
| 308 exact low-fold controller (body zero, control only) | K051 | K052 | LowFrame.Trace/Steps |

Native child replies are arbitrary complete typed records. Assertions cover every argument and output coordinate, counts, original order, frame and raw prepared-cache word. Arithmetic values come only from the paired Lean child laws. Native domains are arbitrary raw records and valid finite indices, never a stronger canonical precondition than the actual caller.

K023's complete group shape timed out once and was retired; K035–046 split it into four source segments with explicit adjacent state association. K020's structured-equality prepared-stage failure is excluded; K032–034 use the SAME harness name and check the actual raw nine-word property, calibrated independently by K047/048. K010 was a compiler borrow error, repaired with a source-ordered temporary. K021/022/024/025 were cancelled without launch. See NKG_FAILING_STEP.md.

`NKG_sourcecheck.py` checks the exact four frozen body hashes, token erasures, selected branch/fold control and four group segments. The source-to-native association and typed assertion transport are the existing P6/D188 option-A reclassification, not removal of compiler/extractor trust. Full complete root statements and cut definitions are printed by L051. No isolated native verdict is itself a row closure.
