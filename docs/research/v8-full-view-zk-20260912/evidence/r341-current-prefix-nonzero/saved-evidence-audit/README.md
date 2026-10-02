# R341 saved-evidence audit

Read-only audit of the promoted R341 bundle. No Lean rerun or tracked edit was made.

All bundle checksums, source-copy identity, target SHA, compile revision ancestry, run metrics, caps, and three complete axiom reports pass. The recorded compile revision is `37d5dd7ecb2c6f7b98822147522b043884ef77d9`, an ancestor of the later checkout. It compiled with exit 0, 1.57 s wall time, 3,710,056 KiB GNU-time child RSS, zero swaps, and 5G/7G/0-swap/128-task caps (`-j1 -M4500`). All three axiom outputs contain only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem headers are algebraic: only field-valued functions, indices, and positive natural lengths appear. They establish exact nonzero criteria for symbolic prefix products; the actual source zero-detection traversal and any caller success remain unproved. One failed `rfl` attempt and its source/log/receipt are preserved and contain `sorryAx` only in that rejected output.

An initial scope matcher incorrectly rejected the explanatory word “iterator” in the module comment; the corrected check inspects theorem headers directly. See `rejected-check-expectation.json` and `audit.json`.
