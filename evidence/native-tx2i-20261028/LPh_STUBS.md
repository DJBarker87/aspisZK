# NBS substitutions and domains

Inherited NBQ substitutions retain their original qualifications and paired theorems; NBS_REUSE.json pins those reports and modules. No new headline premise is removed.

| Stub / native use | Paired emitted-ok Lean theorem | Domain and observation |
|---|---|---|
| NBS_route::cm_mul for CM31::mul (K007) | AspisR1.LPi_FieldValues.cm_mul, via AspisR1.LPi_CMProduct.source | Four canonical input coordinates. K004 verifies all TABLE_A/B coordinates canonical, K007 asserts this domain at the actual call. Stub returns kani::any coordinates constrained to realWord/imagWord. LPm_StubBounds.product/canonical_sum proves wrapping formulas equal the natural specification. Exact selected TABLE_A[u&511], TABLE_B[u>>9] operands and exact returned x/y checked. No native field multiplication proof. |

K008's after-product program cuts are not function substitutions: every product is a symbolic u64 ≤(P−1)^2. NBQ_RawCell.arithmetic proves the exact emitted checked multiply/add law; NBS_DotTerm.update is intended to compose all eight on the same state. Until that theorem compiles and the source-step association is recorded, K008 is a local cut window, not whole-helper closure. No product equation is silently assumed as caller evidence.

## Final associations and rechecks

NBS_DotTerm.update and NBS_NativeEight.source now compile (L088/L094), so the
joined eight-cell cut is associated with the exact adopted model Result, under
its explicit canonical/count/pre-state bounds. K028 rechecks that native window
with KMX. NBS_DotInner/Outer/Tail/Whole/Four are checked model compositions, not
an independently established whole native execution.

| Additional substitution/cut | Named Lean result | Domain and final credit |
|---|---|---|
| NBS_route::base_mul, M31::mul (K010/K032) | AspisR1.LPf_BaseMultiply.source | Both operands are SAME returned fibre x, canonicality asserted at the call and derived from the preceding cm_mul specification. Any reply constrained to natural product modulo P. K032 passes with KMX. No field multiply implementation is executed in Kani. |
| NBS_geometry::base_mul (K012; full backward gate unlaunched) | AspisR1.LPf_BaseMultiply.source | Canonical product/selected flat value or suffix/prefix value. K012 times out; no full-step credit. The paired theorem exists, but the parent run is not a pass. |
| NBS_tail::push/finish (K023/K030) | NBQ_U06.push/finish; NBQ_TailDomain.three; NBS_DotTail.source | Non-field callee overapproximation: SAME receiver/count and full selected operands; private accumulator words havoced. Actual model values/state chain are derived in Lean, not from havoc. Finish returns any canonical value to prove caller forwarding/addition for every possible reply. K023 passes; corrected K030 times out, so full native tail remains OPEN. |
| NBS_buffer::denied and forbidden_resize (K026) | NBC_Filled.result on Err; NBP_FilledPorts.allocation | Existing allocator Err outcome, arbitrary requested n, actual u32 filled specialization. Reserve gets SAME n and empty receiver; resize must be unreachable. This is an error-port bridge, not universal allocation failure or positive-size buffer initialization. |
| NBS_geometry_cuts backward/prefix field-call cuts (K033/K034) | AspisR1.LPf_BaseMultiply.source; Port4C_PrefixMeaning.total; Port4C_BatchInverse.backward_exact | Arbitrary pre-state and explicit same source operands. No field multiplication is executed and no arithmetic property is inferred from an unconstrained reply. Native buffer/state updates are checked separately; full parent source-step association remains OPEN. |
| Six KMX value-copy hooks, NBS_copy module | KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame/append_spec/realloc_prefix (retained KMX_L003 receipt) | T:Copy, matching lengths, valid aligned nonoverlapping regions and valid owned allocator layouts/positive realloc sizes. Harnesses construct typed live arrays/Vecs; copies stay within their capacities. Realloc has the existing allocator trust boundary. No capacity/address/ownership equivalence is supplied by the KMX value laws. Hook source and controls pinned in NBS_KMX_IMPORT.json. |

K026–029, K031–040 pass under the applicable KMX hooks. K030 is a retained
TIMEOUT, never credited. Original properties/assumptions are unchanged in the
rechecks; NBS_COPY_RECHECK_PLAN.json records their identical body hashes and
adequate element/byte-prefix bounds. K040 is a new arbitrary-prestate getter
check for all counts≤22, all valid offsets and all five lanes. Safe reference
validity is supplied by the actual live typed Vec construction, not integer-only
address claims or a forged guard. Inherited callee qualifications remain.
