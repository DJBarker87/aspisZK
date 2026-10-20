# Four outer callbacks each reach the inner N=8 P6 trace

The checked theorem `generatedFourDotsN4_success_four_innerN8_readbacks` starts from one successful N=4 `arrayFromFn` call using the composed N=4/N=8 P6 operation adapter. It obtains the four ordered generated callback calls from the retained four-step trace. For each callback, success inversion of the actual emitted body yields success of its exact N=8 `arrayFromFn` field operation; the N=8 result adapter supplies all eight ordered limb reads and `m31ReduceU64` results.

This closes the composition and source-call frontier between generated four-callback success and the N=8 reduction facts. It leaves outer accumulator/update arithmetic to the existing S4 proofs. The P6 operational model's correspondence to Rust `core::array::from_fn` remains explicit and open. The theorem does not establish whole S4 source closure.

The focused Lean 4.32 target exited 0 in 2.908 seconds, peak RSS 2,337,751,040 bytes, swap 0. Both `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact source/import/compiler pins are in `manifest.json`; command, preflight, output, and time log are retained under `receipts/`. No object binaries are included.
