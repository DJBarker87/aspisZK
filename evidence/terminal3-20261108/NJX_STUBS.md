# NJX paired-stub register
Exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No new copy stub; no contracts, Option<fn> or writable static. Multiplication never runs in Kani.

|Stub|Full emitted Result law|Caller-established domain|
|---|---|---|
|prepared constructor|NJB_PreparedLaws.new_result|SAME canonical high/lambda power, internally derived|
|prepared product|NJB_PreparedLaws.mul_result|SAME9word PreparedFor from actual constructor, canonical operand|
|QM31 add/sub|NJB_StubLaws.qm_add/qm_sub|SAME canonical operands, prior Result establishes intermediate canonicality|
|M31 lift|FIw_ScalarArithmetic.lift_run/lift_value (RPv owner)|actual expected word<P, no opaque lifted reply|
|pack base4|NJB_PackLaw.result (NFT_Pack)|SAME actual four canonical residuals|

NJX_TailExpr.source discharges every tail product/add/sub on one cache packet. Digest residual cell/source supplies all lift/sub laws; full242/245/246caller composition remains OPEN. Any native stub without its domain/Lean association is SUPPORT only.

Final support windows K005..K032 use local call logs for exact source windows, not unconstrained root replies. Complete natural-number field domains/Results must be supplied by NJX_InitialPrologue/InitialLane/AppendTargets and NJX_RangeStep plus RPv_JFy_SquareTotal.source before parent composition. K021/022 has no credit. Initial constants/chunks/conservation selector caller/cohort association is OPEN; no stub in those support windows is claimed as a closed parent field bridge. See REMAINING for each missing caller domain/association.
