# Multiplication abstractions and approved copy stubs

No NEV Kani harness substitutes or executes a field multiplication. Prefix append proofs call the actual Vec::push only. Field arithmetic is imported from NEI_/NEG_, never reproved.

| Native abstraction / stub | Paired Lean law | Domain and use |
| --- | --- | --- |
| Imported NEI_prefix_step::product_reply local record in NEI_K007/K008 | NEI_PrefixProduct.actual; NEI_PrefixWindows.specialize_field_reply | Every raw U32 lhs/rhs; actual emitted M31 multiplication returns ok with their natural product modulo2147483647 and canonical reply. The actual prefix read chooses the same operands; no field arithmetic is executed in Kani. These original receipts retain their names and domains. |
| Exact KMX_copy_nonoverlapping | Existing KMX_CopyMeaning loop/copy value laws, specialized by NEI_PrefixWindows.surviving_copy where needed | Valid disjoint pointer ranges and admitted typed representation. Exact upstream KMX patch/file hashes are checked per native run; matching negative controls are mandatory. This is a copy stub, not a field stub. |
| Exact KMX_realloc | Existing KMX_CopyMeaning.realloc_prefix | Valid allocation layout; successful reallocation preserves min(old,new) bytes and failure preserves original allocation. Prefix's active push has spare capacity and must not grow; capacity/pointer observations are proved. This is not a field stub. |

Patch sha256: bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No custom copy stub, mutable static, Option<fn>, proof_for_contract, or stub_verified is used by NEV prefix proofs. No suspended/quarantined predecessor native receipt is restored.

## Accumulation draft additions (no caller credit until receipts and transport close)

| Local native abstraction | Paired Lean theorem | Domain |
|---|---|---|
| `NEV_BasisProductLog::call` at `basis_inner_iteration` | `NEI_PrefixProduct.actual`, specialized by `NEV_BasisRaw.inner_step` | ALL raw u32 operands; theorem derives reply `< 2147483647`; `0 < n <= 32`, `j < n` establishes the native index domain |
| `NEV_BasisProductLog::call` at `basis_outer_scalar` | `NEI_PrefixProduct.actual` (same input twice) | ALL raw node words; theorem derives canonical reply before native `M31::double/sub`; `0 < n <= 32` establishes native doubling bound |

These are local owned call records under rule 16, not function-pointer or
writable-static stubs. No multiplication executes in either harness. The
caller-to-product-log and induction transport remain open until the named
NEV basis bridge and native receipt pairs validate. This table alone earns
no CLOSED row.

| Local accumulation call record | Paired emitted-definition theorem | Caller-established domain / specification |
|---|---|---|
| `NEV_TailLog::product` | `NBG_FieldDischarge.wide_qm`; nominal binding `NEV_AccumulateCallees.wide_product` (L032) | Canonical eight-word `value`; arbitrary raw QM right input is normalized. The imported theorem returns `ok out`, canonical output, and exact `mulQ`/`modQ` natural-word value on both halves. |
| `NEV_TailLog::add` | `NBG_WideCarriers.wide_add`; nominal binding `NEV_AccumulateCallees.wide_add` (L032) | Canonical old rhs and SAME product returned above; exact two-half `addQ` natural-word specification and canonical output. |
| `NEV_TailLog::power` | `AspisR1.LPi_TowerValues.qm_mul`; nominal binding `NEV_AccumulateCallees.qm_product` (L032) | Canonical SAME old power and prepared rho; exact `mulQ` word specification and canonical output. |
| `NEV_PushCallLog::call` | Imported `NEI_PushRawBridge.complete` / `NEI_PushBridge.complete`; nominal binding `NEV_AccumulateCallees.push` (L032) | SAME BW carrier, row index below 64, canonical power and basis, and phase/residue `NEI_PushBridge.Domain`; the independent local counter, not global query index, determines the four-term phase. |

The native records quantify arbitrary canonical replies; the listed Lean
existence/value theorems specialize those universal context properties to
the actual emitted field results. No multiplication or arbitrary function
contract is proved in Kani. Caller domain proofs and full composition remain
OPEN until the accumulation packet validates; a table entry alone is no pass.

## Dot auxiliary and pending caller logs

| Owned local cut | Paired Lean law | Exact domain/status |
|---|---|---|
| NEV_RawLog.call | NEV_QRawAssociation.actual/cohort; LPi_RawValues.source; NEV_DotPush.complete | Canonical private Q inputs; arbitrary u64 reply coordinates cover actual raw return. No multiplication in Kani. Aux validated; whole dot caller remains OPEN. |
| NEV_DotLog.call | NEV_DotPush.association/complete | SAME canonical private-Q operands and arbitrary owned sums. Full actual receiver/count/order checked by K052/K053; input domains derived by NEV_EbyDomains.value/scalar. |
| NEV_DotCellLog.call | NEV_DotScalar.product | SAME actual widened u32 operands, both canonical; exact checked product returns natural product<=B. K058/K059 only multiplication-free frame/add/log. |
| NEV_TailParserLog.call | CLOSED NET parser packet/window certificates (commit96ac88e728), exact same608-byte subwindow | Native window records original buffer pointer/start/length16; reply None or canonical QM31. Whole caller propagation into the actual parser is still OPEN; no standalone arbitrary byte array or independently chosen actual reply credited. |
| NEV_TailContextLog.push/finish/add | NEV_EbyPushAssociation.source / NEV_EbyDomains.total; NEI_DotFinishValues and retained finish packet; NBG_WideCarriers.wide_add | Full arbitrary receiver/counter/raw rows, canonical reached field operands. K066/K067 plus K068/K069 only local cut credit. SAME selected g read, complete StepBy and native full caller association remain explicit. |

K062/K065 timeouts excluded. K070 lacks a matched negative and earns no native credit. No log is promoted into a completed dot caller bridge.
