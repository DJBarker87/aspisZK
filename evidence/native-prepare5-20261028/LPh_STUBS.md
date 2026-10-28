# NCH stubs and native contract domains

KMX supplied patch SHA256: bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No own copy stub was written. All native calls below use the frozen lock, offline graph validation and post-lock check.

| Stub or contract | Lean pairing | Domain and exact status |
|---|---|---|
| unchanged KMX_copy_from_slice/copy_nonoverlapping | KMX_CopyMeaning.copy_prefix/copy_frame; NCA_SemanticFrames.window/root | initialized valid disjoint byte slices and equal lengths. Array32 K010–K018, header5 K019–K023/K028–K031, low16 K032–K036, composed K042–K045 have positive and failing controls. |
| NCH_zerohigh contract | KMX value semantics of indexed zero writes; NCA_SemanticFrames.window | actual16-byte initialized mutable array; selected j<16. K037–K041 fidelity complete; modifies violation detected in native memset. |
| NCH_arraycopy/NCH_headercopy/NCH_copylow | NCH_WindowLift.compose_suffix/row_suffix plus unchanged NCA frame/restoration/loop | exact sized borrowed32/5/16 regions. Every stub_verified family has inverted ensures FAIL, unimplied caller FAIL with real-body PASS, and modifies violation FAIL. Slice32 K006/K009 ICE is excluded; expand-cell aggregate K026/K027 TIMEOUT excluded. |
| NCH_mul opaque WideExact::mul | NCH_OpaqueProduct.instantiate; LPi_TowerValues.wide_mul (direct emitted FIo_Native natural-word law) | universal flow for arbitrary bit-valid operands/reply at K046; Lean semantic substitution requires canonE of BOTH operands and produces canonE reply and ew reply=mulE(ew x)(ew y). Actual powers scalar domain/invariant remains inherited LPi_PowersStep/LPi_PowersPrefix, not supplied by the stub. K047/K048 wrong-flow/reply controls FAIL. No native multiplication proof or arithmetic constraint. |
| NCH_check/NCH_tail scan cuts | NCA_AcceptedScan.source / NCA_CheckPort.y1; actual callee bridge still separate | SAME full57607 proof, Y1 pointer7031/length464, then first wide check7495/32; cuts log order and stop; no successful scan invented. K001 with K002/K003 controls. |

All call cuts overapproximate child Results; none is credited as an implementation of that child. Exact native source/fission/carrier association remains explicit where not yet proved. Runtime allocation/ownership/digest realization is retained in statements1/3, never inferred from these value laws.
