# Premise and scope change

Before: ReaderK's concrete adapter invoked the retained FullV10 QM decoder. Its successful-output canonicality was proved, while current-Rust decoder correspondence remained an explicit boundary.

After: for the exact newly extracted current QM decoder, the sole execution premise `current_decoder bytes = ok (some q)` yields retained-decoder same-value success and canonicality. Two CM-success witnesses are derived from that same premise, not assumed. For the current-shaped reader the sole premise is its successful call, and the conclusion preserves both value and cursor.

Retained: explicit raw Reader operation; caller/source-runtime and adoption boundaries; existing decoder/arithmetic and extraction-tool trust boundaries; successful-run scope. Added: no mathematical/cryptographic assumption.

Changed conclusion from rejected candidate: the attempted all-outcomes Result equality for QM was not proved. It is replaced by an explicitly weaker accepted-run transfer, sufficient for the local canonicality obligation. CM all-outcomes equality was proved. Neither local proof transfers an adaptive security experiment by itself.
