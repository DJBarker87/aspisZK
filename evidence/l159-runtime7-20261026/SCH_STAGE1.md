# Stage 1: direct per-oracle interpretation and TX1 inversion

`SCH_SourceFirst.accepted` (033) derives owned stage1 success from accepted IDEAL wrapper success, preserving the exact saved checkpoint and entry. It uses `SCH_Lower.result`, the all-constructor `SCH_IdealSdkInvoke.invoke`, and symbolic pure-operation preservation. No reverse application of SCE_NativeFirst, syscall totality, native success or security assumption is introduced. The output dictionary is explicitly SCH_IdealSdk.dictionary c hashv H, not silently the fixed native dictionary.

`SCH_Oracle.evaluation` and SCH_OracleErase.result expose ideal source semantics with exact ordered reads and error results. SCH_WrapperFirst/Second invert actual ideal wrappers, including reserve failure, copy panic, cleanup failure and verifier errors. SCH_TraceExists produces a trace from acceptance, never an independent successful witness.

`SCH_OracleQuantifier.not_all_worlds` (026) checks the ACTUAL retained P1 type: for fixed sha256, it is impossible to have P1 sha256 H for every H. Pointwise P1 forces sha256=H. This rules out simply universalizing the supplied fixed-native observations; it does not refute a separately proved ideal-source transport theorem.

Attempts001–035: failed development results remain excluded in receipts, including default heartbeat failures003/005/020/030 replaced by split declarations or symbolic helper rewrites; no cap/heartbeat/depth increase or unchanged timed-out rerun. Top theorem and ledger unchanged. The uncompiled second-source/log extensions are continuing stage2 work, not claimed here.
