# NJB field and copy boundaries

Target not yet established. No field multiplication executes in Kani. Every log lives in a harness-owned mutable record; no writable static or function pointer.

| Native replacement | Paired complete-Result Lean law | Domain |
|---|---|---|
| NJB_Ops::NJB_mul / event kind0 | AspisR1.NJB_StubLaws.qm_mul (L013), from JFy_FieldTotal.mul | both SAME operands Canon; output is ok, canonical and decode z=decode x*decode y |
| NJB_Ops::NJB_add / event kind1 | AspisR1.NJB_StubLaws.qm_add (L013), from FIv_PreparedTotal.add | both SAME operands Canon; output is ok, canonical and decode z=decode x+decode y |
| NJB_Ops::NJB_sub / event kind2 | AspisR1.NJB_StubLaws.qm_sub (L013), from JFy_FieldTotal.sub | both SAME operands Canon; output is ok, canonical and decode z=decode x-decode y |
| core::ptr::copy_nonoverlapping | exact KMX_copy_stubs.patch, NJB_KMX.sha256; KMX_CopyMeaning value/frame laws | valid Copy source/destination geometry; no new copy stub |

Native cuts quantify universally over canonical reply words and certify movement/indexing/order only. Lean instantiates those replies with the actual emitted operations via these laws; arithmetic equality is never a native assertion or an independently assumed endpoint. This is the opaque-call-log use of rule A and (ai)/(aq); P6/D188 option-A semantic transport is retained as reclassification, not removed trust. The natural tower interpretation underlying decode is the retained FIv/JFy proof; no unsupported claim that a native multiplication was verified.

NJB_residual establishes canonicality of all10 input Q values and17 replies before executing the cut. Each operation asserts its two operands canonical; the model root derives intermediate canonicality from the paired laws. K006 passes and K007 fails in the exact KMX/deployed configuration. The active windows use the same domain on every high/low/accumulator cell and reply, which NIH_AtPoint supplies for constructed selectors; their mutable pre-state invariant must be established by the Lean induction.
