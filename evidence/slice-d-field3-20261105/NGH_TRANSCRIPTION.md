# Reference transcription boundary

The additional ruling-(ah) trust is the hand translation from prefix-owned Rust references to Lean definitions. This is distinct from the retained compiler/Aeneas/source-to-ELF trust. It is not an emitted-body proof; no helper extraction is attempted.

NGH_reference.rs.txt is frozen helper structure with prefix-owned names. Exact source hashes are in NGH_INHERITED_PINS.json and the current evidence manifest. The correspondence is:

| Rust reference statement | Lean reference statement | Checked support |
|---|---|---|
| left/right component sums, cache arrays | NGA_Cache.prelude on each same receiver | NGA_Cache.prelude_source, NGA_CacheDomain.source |
| nested component/channel order 0..3 | NGH_AccumulateRef.cells NGA_Nine.trace | NGA_Nine.trace_nodup / trace_complete; NFT controlled order |
| selected checked U64 product then +=, all other cells preserved | NGA_Cell.step, one arbitrary Cell | NGA_Step.source; NFT_K028/029 |
| return the same sums array | NGH_AccumulateRef.run | cells_eq / model_eq, NGA_ArrayExt.source |
| zero 3x3 array, index=0 | NGA_Small.zero, initial empty processed prefix | NGA_Small.zero_value / source |
| index<N: same left[index],right[index], then index+=1 | NGH_SmallRef.loop on ordered indexed pairs | NGA_Indexed.same_inputs, NGA_OuterStep.source |
| final converter on sums | NGH_SmallRef.run, NGA_SmallResult.convert | NGA_Converter.value, NGA_SumAlgebra.source |

The functional list traversal states only the semantic loop order. It does not purport to expose private Rust iterator fields. Native association and actual function contracts remain separate gates; a model equality cannot satisfy them.

QM31 square is loop-free and already has an emitted definition. NGH_QSquareRef.run is the sequence CM square(c0), CM square(c1), mul_by_r, CM add, CM mul(c0,c1), CM double; model_eq is exact emitted-body equality. The local native record preserves the same source order and operands with three opaque product replies. That ordinary ruling-(y) association does not invoke the handwritten-helper exception.
