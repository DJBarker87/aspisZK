# Finish-round fission: corrected V2 two-round range closure

This packet records the corrected V2 helper adapter, its two-round loop
success result, the finish-success join, and the literal Aeneas range facts
that close the S2 range premises. The V1 adapter is retained only under
`diagnostics/superseded_v1/`: it selected alpha before the comparison guard,
which does not match the generated/Rust evaluation order.

The accepted result is `AspisR1FinishFissionLiteralRange.s2_success_fission_model_no_range_hypotheses` in
`sources/FinishFissionLiteralRangeV1.lean`. It instantiates Aeneas
`IteratorRange.next` for `[0,2)`, `[1,2)`, and `[2,2)`, then applies the checked
V3 same-record finish-success join. The output retains the exact two round
equations and alpha entries, with no free iterator-next or range hypotheses.

`sources/check_finish_round_helper_adapter_v2.py` checks the full generated
helper body against the V2 adapter after an explicit list of callee/operator
substitutions. It checks operands, bindings, branch shape, return, and order;
the alpha array read remains inside the successful comparison branch. This is
a structural correspondence check only. It does not prove Rust/Aeneas
operational equivalence, connect the candidate helper to production caller
reachability, or prove that the fissioned candidate is equivalent to the
frozen production `finish_relation` body.

The Rust and generated Lean extraction inputs are an isolated source candidate
assembled for the helper cut. They are not a production source revision.
Generated Funs/Types are included as textual extraction evidence, but the proof
closure does not import `FunsExternal_Template` or rely on generated external
stubs. All Lean proof receipts report only `propext`, `Classical.choice`, and
`Quot.sound`.

## Green proof receipts

| Module | Source SHA-256 | OLean SHA-256 | Exit | Wall | Peak RSS | Scope peak | Swap |
|---|---|---|---:|---:|---:|---:|---:|
| `FinishRoundSelectorSemanticV1` | `e7e56eda53bce7239a56750182c6ead4da8b0a49b7ea68e35d4334ef35f1a390` | `7adcb94d65eab3aad02bd62c1faba31af7c3ab9395caf6d474696937c9260db9` | 0 | 1.104s | 2,367,848 KiB | 288,292,864 B | 0 |
| `FinishRoundAlphaSemanticV1` | `fa8260fde6ab3fb86cc4f53edc69faa801b3e0c2c25100dbd98c9df1750b989c` | `6506f67c49631e66812ba65a95ea7c8a37b606dc97924600ffbbe24c3fc84233` | 0 | 1.205s | 2,371,412 KiB | 287,739,904 B | 0 |
| `FinishFissionHelperAdapterV2` | `76ad3ab83acb25b3245fde2d437c10f8ac3d2a2bc0f5be9573618b9604bfb612` | `f5fe8654036a828a3c308014677a981906a43f0fdd2318700c25604118b063a5` | 0 | 1.404s | 2,385,460 KiB | 296,607,744 B | 0 |
| `FinishFissionHelperLoopV2` | `2a445084fb955b2f215305665c2333c813b87d0994e5932d7175f6034d8d8de0` | `5ea6c827bd87462ef33ef5620e48852250bb1bd214958936667a68ee5b96cebf` | 0 | 1.204s | 2,371,556 KiB | 286,781,440 B | 0 |
| `FinishFissionSourceSuccessJoinV3` | `b262de9c9d6a4694479faed624414705f8bc38a5e732d90d65f45dfc35c76cc2` | `22f9b1dbfc5d0b24a6fef7b58513e0b513601d60f1bc839ea8779259f7485859` | 0 | 1.405s | 2,382,360 KiB | 300,302,336 B | 0 |
| `FinishFissionLiteralRangeV1` | `3b6c9f8c70ff77e524ac219d0f126975610a2728b5d19d675e982568e468ebe9` | `72c3a92af6b014367f3755f16bf15e2c08bf8f23c655e82132bda935df8110f7` | 0 | 1.906s | 2,386,028 KiB | 328,744,960 B | 0 |

Per-run commands, preflights, receipts, Lean logs, and time logs are under
`evidence/`. The literal range module reuses the already checked Aeneas
`next_UScalar_some_spec` and `next_UScalar_none_spec` proof shapes from
`OccupancyRangeTraversal`; its copied local lemmas have no `sorry` or added
axioms. Direct source/object import pins are in each preflight/config and
summarized in `manifest.json`.

The range-check packet is a focused model closure, not a final proof that the
candidate fission helper is reachable from the production verifier. Pairing,
dot-product, and remaining outer finish obligations are outside this result.
