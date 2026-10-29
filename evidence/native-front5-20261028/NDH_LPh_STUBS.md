# NDH stub/domain table

No field multiplication is executed or stubbed in any NDH Kani attempt. No `stub_verified` substitution is used. No contract over a new Result/slice/Box/Vec shape is admitted for call-site substitution. The Result-of-array finish packet is OPEN pending the three required shape controls.

| Stub / reused law | Domain and pairing | Use |
|---|---|---|
| KMX_copy_from_slice | Exact approved patch `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`; valid equal-length initialized disjoint slices, Copy elements | K001 positive / K002 false-copy control. |
| KMX_copy_nonoverlapping | Same exact patch; valid initialized source, writable disjoint destination and count, Copy elements; inherited KMX_CopyMeaning value laws | K027/K028 generic pointer controls; native call/reply, array and record packets with their per-property negative controls. No custom copy stub. |
| KMX_realloc | Same patch; allocation preconditions, preserve old allocation on failure and min(old,new) bytes on success | Empty/singleton heap diagnostics K069–K071 only; no full heap.filled bridge. |
| LPk scalar integer facts (not a new NDH stub) | K008 quotient bound, K009 remainder bound, K020 sparse reconstruction. `NDH_INTEGER_REUSE.json` pins the frozen-lock/graph receipts and copy-/pointer-free reached arithmetic. `NDH_Arithmetic.relation/native_pack/native_cast`, `LPk_Cohort.step_result`, `LPk_Step.unique` discharge natural machine semantics | One division-pass step/trace composition. Old LPk whole-array/from_fn traversal passes are NOT reused for copy credit. Initial remainder0 and every returned remainder<P establish the next scalar domain. |
| Future M31 multiplication companions (NOT run) | `AspisR1.LPf_BaseMultiply.source` returns the concrete emitted M31 product modulo P; `NDH_Pow5.value` gives its three products and canonical intermediate/results | pow5 remains OPEN until a native opaque-call log with caller canonicality exists. These theorems do not mean a native field product was proved in Kani. |

Runtime digest probes use statically selected record backends to check the exact call descriptors and unchanged reply. SHA's value is the existing RuntimeSha256Value realization. LegacyHashFn/function-pointer-dependent contexts receive no credit. No Option<fn> verdict is used or renamed.
