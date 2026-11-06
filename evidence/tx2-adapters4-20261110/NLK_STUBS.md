# NLK oracle and stub inventory

Target not yet established. No multiplication is reached/proved in Kani; no
field-operation stub is installed. No function contracts/stub_verified, writable
static, Option<fn>, Ref/RefMut-return or Result<Box>-return substitution is used.

| Mechanism | Law / scope | Status |
|---|---|---|
| Exact canonical KMX_copy_nonoverlapping | mitigation patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; existing KMX value laws through NLF_CopyValue.copy_coordinate/copy_frame/copy_whole | Applied to all native configurations; matched controls required per cut |
| PDA local syscall oracle | pinned deployed SDK source a667b28ce392328ef9ef3a6a4ef24606e9c764d58c9c536afe1d22a191898a24; NLK_PdaAbi.complete_input and status lemmas reuse NLA_PdaStatus | K005..K010 control pairs, statuses0..2 and2..5 seeds; unsupported-status source abort still retained separately, no PDA value law |
| Registry local typed decoder/PDA oracles | exact source-ordered branch certificates; NLA_DataPrefix all-arm mapping and existing CLOSED child packets must be instantiated at SAME byte/seed arguments | Intermediate branch cuts only, not row closure |
| Lane loop_summary | NKP_LaneInduction.compose and NLA_LaneAssemble.source_steps from the native one-iteration cuts | K025 whole-invocation shape timed out and is retired; no credit from this run |

K021 failed canonical-copy unwind in OWN harness setup (to_vec128), not the
program branch. The changed setup uses Box<[u8]>::into_vec to transfer ownership
without that bulk copy; no unwind/cap/timeout increase. K022/K023 certify V1;
K024 V2 timed out, replaced by registry/entry halves K026..K029. K032 expanded
233 prefix timed out; it is split by source boundary for subsequent attempts.

K057/58 add unchanged program/output-frame observations; K059/60 cover the
pinned SDK seed-bounds prelude. NLK_PdaSites derives fixed-format caller
domains instead of adding stronger preconditions to a row root. Status>2
still lacks its universal native abort certificate. Four data/decoder pairs
K047..K054 use actual owned234 extents128/192/256/320. Existing CLOSED emitted
decoder laws must be instantiated internally before any such local oracle
cut could participate in row credit. None is a positive root here.
