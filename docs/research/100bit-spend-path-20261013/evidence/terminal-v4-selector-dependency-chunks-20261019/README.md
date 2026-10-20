# Terminal v4 selector dependency chunks (candidate evidence)

This packet records a source-preserving dependency split of the exact generated current `Funs.lean` (SHA `b50b8aec665d47f06ee91b5980807734e0ccf5ef9d993fa50a97a3ac92f0aefd`). The selected root is `pool_v1.pair_forest_copy_terminal.selector_mask_sum_16`, reached by the generated `Selectors.active_literal` and `Selectors.active` functions. Declaration bodies, documentation, attributes, and source order are copied from the generated file; `source-span-byte-identity.json` records verified original byte offsets and declaration-block hashes.

The selector closure and immediate callers compile with the candidate U16 and array-iterator external models. The `evaluate_with_selectors` closure is 47 declarations. Its first three further dependency chunks compile; the chunk containing pattern functions, and the single isolated `COPY_PATTERNS` declaration, hit the existing 4 GiB aggregate Lean guard. No higher-cap retry was made. The next step is a fresh capped build-host admission for the frozen one-declaration `COPY_PATTERNS` source, then continue its dependent chunks.

This is not a complete generated terminal method check or source-correspondence proof for the external U16 / array iterator models. The full generated Funs attempt and prior U16/IntoIter candidate packet are retained separately at `../terminal-v4-u16-intoiter-models-20261019/`.

Green focused outputs and exact attempt receipts are included; failed diagnostic attempts are retained unchanged. No production Rust source changed in this packet.
