# S4 four-slot Current array semantics

This focused theorem lifts the concrete one-slot callback field theorem to the exact four values retained by one successful returned Current array. Given the same 608-byte C1/C2 opening encoding, the same 29-entry coefficient powers, the actual returned four-element array, and its four `LiteralFieldResult` witnesses, it proves that mapping the Current decode over that array equals the four local width-29 batch values in slot order.

The proof applies the concrete same-callback width theorem independently to the four already-retained slot witnesses. That theorem derives parser and tail scalar meanings from the callback's own source witnesses. This packet adds no independent parser-success, scalar-value, or child-run premise.

The RHS uses each slot's local decoded C1/C2 word. Root's separate recovered-opening and returned-array transport theorems connect this local list to the global first-fold fibre. This packet does not claim that final global transport itself.

The direct imports are the green concrete width-29 callback kernel and the accepted CandidateQueryFieldEvidence definition. Their exact source/object pins are recorded in `dependencies/import-pins.json`. The focused Lean 4.32 check used the kernel's recorded coherent LEAN_PATH with the kernel object directory prepended. No compiled objects are included.
