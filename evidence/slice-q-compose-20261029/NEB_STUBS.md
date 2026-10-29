# Selected stubs and domains

| Native stub/cut | Exact selected domain | Named emitted/cohort theorem | Caller establishes it |
|---|---|---|---|
| NEA_point::cm_mul | both CM31 pairs canonical; universal canonical reply | NEA_FieldProduct.emitted_cm; NEB_GeometryFieldPorts.physical/cm_eq | K017 native assertions and exact operand log; NEB_ActualGeometryPoint.calls derives actual selected table operands canonical |
| NEA_line::point_cut | same u<262144; canonical two-coordinate reply | NEB_ActualGeometryPoint.calls/frame | K029 cut asserts admitted u and records that same u/reply; root PacketDomain preserved |
| NEA_line::m_mul | canonical x/y, universal canonical reply | AspisR1.LPf_BaseMultiply.source; NBG_InverseBridge.mul_eq_probe | K029 logs both exact point.x operands; NEB_ActualGeometryLine.calls derives them and canonical square |
| NEA_line::m_double | canonical scalar | NEA_LinePrimitive.double_value; NEB_GeometryFieldPorts.double | K029 stub asserts domain; NEB_ActualGeometryLine.calls derives square bound |
| NEA_line::m_sub_one | canonical scalar and rhs exactly1 | NEA_LinePrimitive.sub_one_value; NEB_GeometryFieldPorts.sub | K029 stub asserts both; source ONE and NEB_ActualGeometryLine.calls derive the exact arguments |
| verified M31::add/sub | both input scalars canonical | NEB_WordRefs.add/sub and NEB_AdditiveFrames; actual K011/K013 contracts | Each K016-K031 actual caller executes the requires check; exact canonical projections/earlier outputs in NEB call witnesses |
| approved KMX_copy_nonoverlapping | original approved Rust safe copy domain | unchanged KMX value/frame laws in the approved mitigation packet | exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; matching per-packet positive/negative controls |

No field multiplication is proved in Kani. No new multiplication stub was authored in this lane. The imported product/point cuts overapproximate canonical replies, so their emitted value law selects one permitted exact reply. Imported scopes have distinct ghost relations; source-level state/effects exclude only cfg(kani) ghost instrumentation. Historical failed and timed-out encodings provide no credit.
