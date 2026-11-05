# NHX opaque calls and paired emitted laws

Local-record opaque-call logs under (y)/(ai), no native multiplication, no writable static, no function-pointer contracts, no stub_verified. Arithmetic/child replies are interpreted only by the following SAME-call packets; logging nondeterministic replies is control observation, not arithmetic proof. All values/domains are threaded source-order, never independently selected child witnesses. Retained NHM_LPh_STUBS.md and NHI/NHE packets remain authoritative for their internals.

| Stub/log family | Emitted definition and named Lean law | Domain / caller discharge |
| --- | --- | --- |
| qm / tqmul | FIo_Native.aspis_core.field.QM31.mul; AspisR1.LPi_TowerValues.qm_mul (ok, canonical, exact natural mulQ) | Both SAME canonical Q inputs. NHI_FactoredProducers.total gives every producer call, including unused q^4; NHM_FactoredDomain.producers binds extra[side]; NHX_FactoredSuffix supplies q16*q4. |
| qs | FIo_Native.aspis_core.field.QM31.square; NGH_QSquareRef.model_eq/cohort, NHI_FactoredProducers.square | SAME canonical Q input, produced by preceding mul/square on the SAME extra. No Kani square or multiplication. |
| tmul / emul | FIo_Native.aspis_core.field.wide_exact.WideExact.mul; AspisR1.LPi_TowerValues.wide_mul (ok, canonical, exact natural mulE) | Both SAME canonical E inputs. NHM_FactoredTerm/Sums, NHX_FactoredTail/Cut/Suffix and NHX_HighDomain.scale/high_reply provide stage domains when compiled/current. |
| tmix | FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31; NHE_ScalarProductLaw.product (ok, canonical, exact coordinate mulQ) | SAME canonical E/Q inputs, including SAME q4/q16 producer outputs. |
| tquarter | FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 at frozen QUARTER; AspisR1.NGM_RoundScale.total (ok, canonical, exact limb modular product) | Quarter=536870912; input E from SAME previous term or ap1[PERM[3]]. The emitted law is all-word; no new arithmetic claim. |
| tadd | FIo_Native.aspis_core.field.wide_exact.WideExact.add; NGW_PolynomialAdd.total/observed and NGW_CurrentAddPort.adopted | Both SAME canonical E operands; native add certificate inherited, never rerun. |
| tscalar / scalar_call | FIo_Native.weights.Weights.scalar_factor; NHI_Scalar.cohort/total | SAME canonical Q[4]/E[4]. NHM_FactoredDomain.low_scalar; NHX_HighDomain.row/scale. |
| child (dispatch) | FIo_Native.weights.s2_grouped_inactive_pair; NHM_GroupRoot.cohort/canonical | SAME2048 canonical-byte-window message and16 canonical low E cells. Exact ptr/len/reply native K044–K051; fallback outside domain. |
| partial | FIo_Native.weights.partial_dot; NHM_PartialDot.cohort, NHM_DotResult.partial_result | SAME2048 canonical-byte-window message,16 canonical common Q cells, side<4. NHM_SharedPartialsDomain derives every side; K052–K059 windows and K042/K043 control. |
| high_call | FIo_Native.weights.high_dot; NHM_HighDot.cohort, NHM_DotResult.high | SAME4 canonical partial E cells and4 canonical coefficient Q cells. NHX_HighDomain.row and inherited shared-partials output; high parent remains OPEN until full frame/error chain. |

A named domain or theorem whose current source has not compiled/audited is OPEN support, never a passed stub obligation. Entire factored/high/process parent rows remain OPEN unless NHX_CLOSED.json explicitly qualifies them. Compiler/Aeneas/Std/allocator/ABI/source-to-ELF and P6/D188 optionA semantic transport are retained/reclassified, no removal. Exact KMX patch hash and negative controls are NHX_SOURCE_ASSOCIATION.md.
