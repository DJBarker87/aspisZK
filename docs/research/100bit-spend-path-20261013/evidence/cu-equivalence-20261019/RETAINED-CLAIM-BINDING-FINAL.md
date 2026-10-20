# Retained claim binding: complete preparation and transaction composition

The previously arbitrary `PreparedCommon.claim` interpretation is now fixed to the actual complete `prepared_claim` source context: actual kappa powers, six checked 29-term dot calls, all seven traced products/additions, and the terminal trace/return. The original and optimized dot helpers use the exact semantic scalar selector and final-message decoder. Coordinate-only carrier/error transports preserve every value and checked error.

The final source endpoints are:

- `CuSavingsRetainedClaimBindingFinal.prepared_equivalence`: complete emitted `Prepared.new`, fixed actual old/new claim contexts and actual sampler/powers.
- `CuSavingsRetainedClaimBindingFinal.tx1_prepare_equivalence`: complete `retained.tx1_prepare` with the exact selector specialized internally.
- `CuSavingsRetainedClaimBindingGammaRho.source_tx1_equivalence`: original `retained.old_tx1` with the fixed original claim to retained `tx1` with the fixed optimized claim and the existing Gamma/Rho optimizations.

No endpoint assumes gamma canonicality, child success, an arbitrary claim interpretation or a candidate-equivalence equation. Gamma origin is obtained from the actual sampler result at its bind; the reusable table is obtained from the actual source power builder at its bind. The theorem preserves earlier failures/divergence without requiring successful preparation. The complete transaction theorem retains the previously explicit 64-bit and sufficient-allocation resource premises.

## Source interpretation and extraction

`check-canonical-vector-context.py` pins the original entire source `prepared_claim` and inversely checks replacing only its complete inner dot with `SOURCE_CLAIM_DOT(point,g)`. The retained source kit then fissions the unchanged outer context into a six-dot `claim_parts`, a seven-term `claim_sum`, and their actual `claim_context` composition. This avoids the unsupported Aeneas loop join between two symbolic-array loops. The initial failed frontend attempt is preserved as `retained-claim-binding-aeneas-a`; the source-factored extraction succeeds in `retained-claim-binding-{charon,aeneas}-b` with no frontend patch or validity-check change.

The nominal emitted field/error carriers alias the existing checked source carriers only after verifying identical coordinate declarations and enum order. Raw Funs promotion adds only runtime dictionary binders; every emitted computational definition remains byte-identical. Actual source Wide.add/mul and power builders supply arithmetic. The dot helper closes over the same immutable gamma table and exact sem/y1 selector. Its fixed callback equality follows from the checked source 29-term dot theorem; the entire emitted outer context then follows by kernel congruence.

The original Gamma immutable-binder source interpretation is checked again and instantiated with this fixed complete source claim context. The final theorem does not leave its source tail as an unconstrained `PreparedCommon.claim` function.

Existing unchanged sampler/hash/transcript/observer/semantic-prefix interfaces and the established Rust/Charon/Aeneas/compiler/library/ownership model remain explicit source/runtime boundaries. The leaf `Trace.value` denotes the unchanged source trace call. This work does not claim a complete machine-code refinement or a new CU measurement and changes no production Rust, proof format, public-input encoding, transcript, or challenge schedule.

## Checked targets

All selected targets exit zero, use only `propext`, `Classical.choice` and `Quot.sound`, and have zero process swaps. RSS is KiB. Exact commands, revision/features, source/object/receipt hashes, direct-import hashes and full `#print axioms` output are in the JSON report and receipts. The eight selected source/import objects are coherent.

| Module | Selected attempt | Wall seconds | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|
| AspisR1RetainedClaimBinding.Types | retained-claim-types-b | 1.403 | 2571020 | 0 |
| AspisR1RetainedClaimBinding.FunsExternal | retained-claim-external-a | 1.804 | 2967480 | 0 |
| AspisR1RetainedClaimBinding.Funs | retained-claim-funs-a | 1.604 | 2979488 | 0 |
| CuSavingsRetainedClaimBinding | retained-claim-binding-c | 2.005 | 3813972 | 0 |
| CuSavingsRetainedClaimBindingPrepared | retained-claim-prepared-d | 7.615 | 4094604 | 0 |
| CuSavingsRetainedClaimBindingSelector | retained-claim-selector-b | 2.005 | 3799512 | 0 |
| CuSavingsRetainedClaimBindingFinal | retained-claim-final-a | 2.005 | 3804880 | 0 |
| CuSavingsRetainedClaimBindingGammaRho | retained-claim-gamma-rho-a | 2.005 | 3812244 | 0 |

## Re-pin inventory

| Source declaration/context | Re-pin declarations/evidence |
|---|---|
| `prepared_claim` complete outer context | `AspisR1RetainedClaimBinding.{claim_context,claim_parts,claim_parts_loop,claim_sum,claim_sum_loop}`, exact inverse-fission/source kit pins |
| Inner six 29-term checked dots | Existing actual `old_callers.claim_dot` / `new_callers.claim_dot`, `CuSavingsCanonicalVectorContexts.six_point_claim_context`, `CuSavingsRetainedClaimBinding.body_equivalence` |
| Semantic scalar selector and y1 decoder | `CuSavingsRetainedClaimBindingSelector.{scalar,select,selected}`, unchanged exact source selector expression/decoder bindings |
| Actual `Prepared.new` and tx1 preparation | `CuSavingsRetainedClaimBindingPrepared.prepared_equivalence`, `CuSavingsRetainedClaimBindingFinal.{binding,prepared_equivalence,tx1_prepare_equivalence}` |
| Original Gamma prefix plus retained Gamma/Rho tx1 | Existing Gamma source emission pins; `CuSavingsRetainedClaimBindingGammaRho.{tx1_binding_equivalence,source_tx1_equivalence}` |

Recheck command: `python3 docs/research/100bit-spend-path-20261013/tools/cu-equivalence-20261019/check-retained-claim-binding.py`.
