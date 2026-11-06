# NKL stubs

logged_verify: explicit-constructor Bool reply, full arbitrary mutation of both idx[16] and val[16][32], exact root/nodes/d/array address log. Intended CLOSED callee: NJV_TX2.TX2_093/NJV_TX1.TX1_127 plus abort packets. Caller bounds d<=12,count<=172; child bytes32*count<=5504<=9216. Application to the actual whole parent remains open. No multiplication stub; no new trust item. Exact KMX copy_nonoverlapping model from the lead patch; matched negative controls in same configuration.

## Scanner substitution table

| Native oracle/model | Complete Lean law substituted at SAME arguments | Domain and frame |
|---|---|---|
| arbitrary_echeck | NKL_CanonicalChildren.echeck_result/echeck_call; NKL_ScanAtoms.source; CLOSED TX1:189/LPl via canonical NFU owner | false flag; original proof windows32/224/2272 and opening tail128. Full Result includes Parse; no mutable input footprint. Domains are NKL_ScanDomains.source. |
| arbitrary_compact | NKL_CanonicalChildren.compact_result/compact_call; NKL_ScanAtoms.source; CLOSED NFU compact child | original464-byte values window; both Ok/NonCanonical and exact From-to-Parse conversion; readonly. |
| Actual M31/K decoders (executed, not stubbed in these native cuts) | NKL_ClosedChildren.scalar/actualK/quadratic; NKL_NativeGuard.source | Every4/16-byte window from original opening832; full Option/payload, including rejection. No canonicality premise. |
| KMX copy_nonoverlapping | Exact lead KMX patch; pinned KMX_CopyMeaning and NCI_KMXFrames value/frame laws | Patch sha bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Value/frame/count/argument negative controls per NKL_SEGMENTS, same deployed configuration; K073/K075 excluded. |

There is no multiplication stub and no Kani field multiplication proof. Logged_verify remains a local Merkle segment oracle whose whole-parent CLOSED-callee installation is OPEN. No free Bool or operation dictionary reaches the scanner root. No new runtime trust row; native-cut semantic transport is retained P6/D188 option-A reclassification.
