# Actual contiguous row-30 payload from successful source parsing

`AspisR1ViewParseProbe.ViewParseContiguousPayload.successful_parse_strict_second_is_one_source_window` starts from the actual candidate `View.parse_with_query_checks` success and its two-fold branch. It derives one jointly bound witness: the returned folded-root array concatenated with the returned round-one bytes is exactly one 256-byte slice of that same input, within its bounds. The first 32 bytes determine the returned hash state, and strict second-record decoding of the entire mapped source slice returns that state and the seven canonical WideExact values.

The root conversion proof handles the actual slice index, TryFrom32 and map_err nesting. Parse-shape identities derive the 32/224 widths and adjacency. The strong `ViewParseBoundContiguousFrame` endpoint binds all interval indices, byte identities, returned root, bounds and strict decoding together. `ViewParseContiguousIntervals` is a weaker compatibility lemma: its standalone interval witnesses must not be treated as input-byte correspondence. The final payload theorem consumes the strong endpoint, using a generic adjacent-slice identity; it does not combine unrelated existential witnesses.

This extends the existing actual-returned-root-strict-second evidence. The parser shape module gains an enriched theorem while retaining its earlier interface. The exact compiled versions of every added module are included below. Existing independently compiled consumers are not claimed to have received a new coherent full release replay; that replay remains due once the complete caller closure is assembled. No production Rust source changed.

This supplies the actual source-byte argument needed by the Prepared constructor path, but does not prove the caller reaches that path or authenticates custody/transcript state. Full Prepared/caller extraction, whole verifier and accepted-spend soundness, privacy and release-artifact correspondence remain open. No full 100-bit implementation claim is made.

All focused checks exited 0 on the capped NUC, with zero process swaps and only standard Lean axioms. The evidence records exact targets, commands, source revisions and hashes, object/import pins, wall times, RSS, reservations and axiom reports. No broad replay was run.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `ParseShapeRound1Root` | 1.409 | 2650892 | 2 |
| `ViewParseRootSlice` | 1.315 | 2651776 | 1 |
| `ViewParseRootSliceBytes` | 1.167 | 2638176 | 2 |
| `ViewParseRootSourceInterval` | 1.084 | 2632372 | 1 |
| `ViewParseRootFrameSource` | 1.596 | 4095728 | 1 |
| `ViewParseRootRound1SourceFrame` | 1.716 | 4099200 | 1 |
| `ViewParseContiguousIntervals` | 1.139 | 2634124 | 1 |
| `ViewParseBoundContiguousFrame` | 1.729 | 4103560 | 1 |
| `ViewParseContiguousPayload` | 1.746 | 4100432 | 2 |
