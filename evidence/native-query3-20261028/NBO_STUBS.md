# NBO replacement and native partition ledger

No multiplication replacement is introduced. All field multiplication stays in the inherited Lean discharge/NBC field-source association boundary; NBF/LPh_STUBS.md is reused unchanged. No field multiplication equivalence is proved in Kani.

| Replacement | Required semantic pairing | Exact native credit |
|---|---|---|
| NBO_open | NBA_Opening on SAME proof and ordinal | Original proof pointer and ordinal; no byte-semantic pass |
| NBO_dots | native four_dots/direct Port3 op20 on SAME q/g | SAME opening/g pointers and arbitrary returned canonical E carriers; no dot semantic pass |
| NBO_inverse | NBC_Geometry/op18, SAME geometry/index | SAME geometry pointer/index and returned inverse; no constructor pass |
| NBO_circle / NBO_line | Native fold/Port3 op17/op16 | SAME alpha, four inputs, inverse and arbitrary canonical result; fold semantic association OPEN |
| NBO_field | NBC decoder/op21 on SAME 128-byte slice and ordinal | Four sequential calls on q[672:800], with arbitrary canonical replies; no decoder semantic pass |
| NBO_update | NBB_Row.source, NBB_RowTrace.native_result, NBB_RowWitness.construct | ONE borrowed row mutation at SAME address; full other-row/limb frame; power/basis/flush routing. Domain is derived by NBF_Domain/Read/Progress/BasisDomain and periodic invariant, not asserted by routing stub. |
| NBO_reduce | S8OwnedP6ValueModel.reducer_total/value_total_model | ALL U64 inputs; four actual value-method reducer calls on SAME selected row. Replies overapproximate every canonical result; unique exact modulo values come from inherited Lean theorem, not this routing check. |

No native callee replacement is counted as a semantic pass without its exact pairing. Decoder/dots/folds/geometry source association remains OPEN pending exact lower bridges. NBO_QueryDomains.Lower and NBO_TailDomain.NBC_Fields name local result-domain statements only, not whole query equality. GeometryDomain and PreparedDomain must still be derived from SAME upstream native producers.

Native capacity projection gates cover every capacity satisfying N <= cap <= isize::MAX/sizeof(T), for raw-row64, weight64, line-z10 and inverse-row10 Vecs. Both slice projections retain pointer/length; Vec metadata stays unchanged. No claim of allocator success on every capacity is made: these are successful-allocation contexts, retaining runtime/allocator admission. The copy extents (2048,1024,40,200 bytes) are below unwind4096. This is allocation-view coverage; native row/finish steps are checked separately on the SAME slice geometry.

K003 combined capacity/store timed out and receives no pass. It is replaced by capacity-only K005-K008 plus borrowed-row K010, not rerun unchanged. K011 executes one actual Enumerate/store with actual BatchedWeights::value and four reducer replies, including exhaustion; emitted back-continuation induction is NBO_Enumerate.from_cursor (inherited S8 implementation). No whole-buffer native finish runs.
