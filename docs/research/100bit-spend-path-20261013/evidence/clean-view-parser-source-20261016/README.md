# Actual candidate parse success implies same-section validation

`ParseSuccessRound1.parse_success_round1_echeck` proves that successful execution of the parameterized generated candidate parser, when its returned variant has two folds, implies `echeck` success on that exact returned `view.round1`, with the non-initial mode. The proof follows both optional-root branches, all intervening Result/Try exits and the actual final returned record. It assumes no success from the universal query-check helper. It does not yet derive the round1 length, root framing, strict second-record decoding or production-parser equivalence.

Candidate H separates owned shape offsets from borrowed slices so that Charon/Aeneas can extract the caller. The complete isolated Rust source and pipeline commands/hashes/receipts are retained. This is candidate source, not an unchanged release or deployed-runtime proof.

The raw generated external templates contain nonstandard axioms. They are archived as extraction output only and are NOT imported by this theorem. CallerStdModels supplies concrete definitions for the five used library templates, CallerFuns retains the other generated bodies exactly, and CleanParameterizedParse replaces the four query-helper calls with one explicit universal function parameter. The two deterministic adapters verify exact retained source reconstruction and parent-body identity. The rejected original dependency cone is not used as release proof evidence.

Pinned Rust/Aeneas library-model sources and their limitations are explicit in clean-cone-reproduction. The current standard-model definitions do not by themselves prove compiler correctness, arbitrary specialized PartialEq behavior, drop/unwind observations or the external query checker. The actual header comparisons use U8. The checked theorem reports only standard Lean axioms.

The already checked SelectorValueLaneTailWritesCanonical source and receipt are included here as a packaging correction: the complete value-family chain imported this module, and its maintained source was not copied in the preceding value-family batch. Its proof is unchanged and has not been rerun.

All focused checks below exited0 on the NUC with explicit memory/swap caps and zero process swaps. Receipts pin exact sources, imports, revision, commands, wall time, peak RSS, objects and axiom output. No broad regression or complete 100-bit soundness claim is made.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `AspisR1ViewParseProbe.Types` | 1.304 | 2647024 | 0 |
| `AspisR1ViewParseProbe.CallerStdModels` | 1.256 | 2637756 | 5 |
| `AspisR1ViewParseProbe.CallerFuns` | 1.899 | 2663572 | 0 |
| `AspisR1ViewParseProbe.CleanParameterizedParse` | 1.26 | 2635372 | 0 |
| `ParseSuccessRound1` | 1.924 | 2671224 | 1 |
| `SelectorValueLaneTailWritesCanonical` | 1.43 | 2997548 | 1 |
