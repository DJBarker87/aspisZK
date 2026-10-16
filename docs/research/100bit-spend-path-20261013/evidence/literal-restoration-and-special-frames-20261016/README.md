# Prefix restoration, source selector row, and special frame order

`LiteralDecoderPrefixRestore` restores actual past messages from the erased transcript, requiring word agreement only for those messages. `SelectorRowCall` identifies the actual generated selector row result with the ten-coordinate tensor product. The three special-frame modules prove first-read ordering for the initial, reseeded, and query rounds, including the actual query-selected successor state.

The QueryAdjacent receipt compiled the full source as `RawCutLiteralQueryAdjacentAxiomRefresh` to add its missing axiom print. Its checked source is maintained under the canonical module filename; its theorem namespace is unchanged.

These are focused prerequisites. The complete restored decoder, current-table word agreement, terminal source correspondence, and numerical soundness conclusion remain separate obligations.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `LiteralDecoderPrefixRestore` | 1.667 | 3632788 | 2 |
| `SelectorRowCall` | 2.006 | 3821812 | 2 |
| `RawCutLiteralRowZeroOrder` | 2.006 | 3655196 | 1 |
| `RawCutLiteralReseedOrder` | 2.56 | 3651424 | 1 |
| `RawCutLiteralQueryAdjacent` | 2.393 | 3655968 | 1 |
