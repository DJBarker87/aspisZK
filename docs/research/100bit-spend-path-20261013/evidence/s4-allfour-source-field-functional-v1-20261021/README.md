# S4 all-four source field functional

`callback_source_field_functional` is a same-witness composition. It destructs one original `CallbackDecodedTrace` exactly once, keeps its same seven-batch list and `ExactTrace`, derives the ordered source indices `[0,26)` and the byte/parser meaning of every contribution from that trace, and rewrites the returned decoded value with the source-product theorem for that same trace.

The result exposes the literal source head product sum plus the literal two-term tail product sum for the callback’s returned value. The included prior attempts preserve import and namespace diagnostics.

This remains an explicit source-model result. Rust std iterator semantics and generated P6/caller operation installation remain open. Verify with `python3 check_packet.py`.
