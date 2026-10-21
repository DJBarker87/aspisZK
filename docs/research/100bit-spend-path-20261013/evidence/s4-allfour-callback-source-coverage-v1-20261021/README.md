# S4 all-four callback source coverage

This packet contains a green generic `ExactTrace` theorem: given one exact source-model trace, its flattened contribution indices are exactly `List.range' start (26 - start)` when that trace terminates at cursor 26; each contribution also retains its source byte slice, parser result, source array entry, and limb meaning.

The public `callback_trace_exact_source_coverage` wrapper separately returns a `CallbackDecodedTrace` and a coverage witness. It does not prove the wrapper’s existential coverage list is the same as the list hidden inside that callback trace. The subsequent composed consumer must destruct a single original callback witness and apply the generic theorem to that exact internal trace.

Rust std `StepBy`, generated extraction/P6 operation installation, and full verifier soundness remain open. Prior failed focused attempts are retained under `diagnostics/failed-attempts/`. Run `python3 check_packet.py` to verify source pins and checksums.
