# Standard-library interpretations

No new trust. Externals in NJS raw FunsExternal_Template are explicit parameters in the compiled body, then concretely instantiated.

- U8 slice/array equality: Op3I_Std.ops.sliceEq/sliceNe use the ordered eqList model. Op3I_Std.eqList_u8 proves exact byte equality for arbitrary lengths; pinned P7 core.slice.cmp.PartialEqSlice.eq_homo_spec is the library semantics. No opaque comparison Bool enters a root.
- Header Iterator::any: concrete Op3I_Std.ops.iterAny/anyList, SAME Unit state and byte!=0 predicate. Reuse NJJ_LIBMODELS.md, NJJ_K005 PASS/NJJ_K006 FAIL for one native next/predicate step and its complete backing/exhaustion law. Op3I_Header.any_exact and structural anyList retain short-circuit order and consumed count; parser discards the returned iterator. This is rule(au)(3), never a fresh producer-association hypothesis.
- ChunksExact and the padding predicate in batch_tree: NJJ rule-3 semantics are reusable only after the actual caller proves width8 positive and maintains the incomplete suffix/frame. No batch_tree root is claimed yet.
- Slice/array copies: pinned P7 model for extraction; native exact KMX patch and matched controls for every copy-dependent property. Batch leaf K018/019 checks an arbitrary salt coordinate and forwarded reply; model copied/source prove the entire salt value.
