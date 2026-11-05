# NHV stub inventory (in progress)

No arithmetic stub or field multiplication is used in these caller cuts.
KMX patch: bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
The exact committed KMX patch is applied to the own frozen scratch. KMX's
copy_nonoverlapping/copy_from_slice replacements are the only copy stubs.
Native positive/control pairs must complete before any native credit.

| Local record | Native reply and footprint | Exact Lean packet / domain | Status |
| --- | --- | --- | --- |
| ResumeLog.resume | Explicit Ok(Box Prepared, Accumulator) or each of eight deployed Error variants; only record args/calls and consume owned reply | NHT_CommonCuts.resume full Result; NFU full resume and primitive same p/a domains OPEN | Cut association only; no callee law installed |
| PowersLog.powers | Canonical 29-E reply; gamma and call count only | NHT_PacketOps.powers 29 p.gamma; NFW_PowersCohort.source, canonical SAME gamma | Native association pending |
| GeometryLog.geometry | Explicit Ok geometry or each deployed Error; exact queries/next/22 | NHT geometry field remains named; closed for_range packet must establish SAME query domain | Native association pending |
| PendingLog.pending | Explicit Ok pending or each deployed Error; exact weights slice | NFW_QueryResume.pending SAME a; actual BatchedWeights::new packet still needs association | Native association pending |

The explicit-constructor cut replies are universally arbitrary on their stated
stage domain; they are never assumed successful. Their constructor/value carrier
frame checks do not prove that the frozen callee returns those values. That
missing equality remains explicit until the named packet is installed. No
stub_verified or proof_for_contract use. No writable static. No asserted
Option<fn>/function-pointer value. Deployed None marks need the matched control
and rename-stability family required by (ae)/(al).
