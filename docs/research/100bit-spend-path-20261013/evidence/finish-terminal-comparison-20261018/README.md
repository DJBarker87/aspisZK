# Successful finish enforces its terminal comparison

`ActualFinishTerminalComparison.terminal_comparison_of_finish_success` derives
the exact terminal, mask, eta multiplication and addition calls from successful
`FinishModel.finish`. The last addition returns the same `running` value as the
semantic rounds. The theorem supplies this equality; it does not assume it.
The two reflection lemmas show that the source QM31 comparison checks equality
of all four stored coordinates. Canonicality is not needed for this comparison.

The accepted v4 check exited 0: controller wall time 3.034 seconds, compiler
wall time 2.32 seconds, peak RSS 2,620,656 KiB, process swaps 0, no watchdog
abort. All three printed axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The receipt records compiler, import
objects, command, memory reservation and source/output hashes.

The root source baseline was `b302c0d49`, plus the exact new theorem source
`c720d7c66d6dcf0277694ae3616a5a68f62193f35781ff03c1d9887854090805`.
The reused workspace receipt retains its older `bdfdfd5d2` baseline label;
it is preserved verbatim, rather than presented as a fresh checkout receipt.
The target source hash and direct import pins identify the checked inputs.
Production Rust is unchanged. Rejected v2/v3 attempts remain under `rejected/`;
their error-generated `sorryAx` reports are not accepted proof evidence.

`RoundModel` and `FinishModel` implementations remain explicit boundaries.
This result does not instantiate their arithmetic, mask, claims or terminal
operations with production code, and is not a complete soundness theorem.
