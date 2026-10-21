# `tx2_authenticated` exact-wrapper operation cut

This packet records a focused Lean proof that success of the emitted
`tx2_authenticated` wrapper reaches the exact `tx2_common` call with the same
arguments, after a successful parse and `Parsed` observer mark.

`accepted_reaches_exact_common` concludes all three facts together:

* `parseShape proof = .ok (.Ok v)` for some `v`;
* `mark obs verifier.Phase.Parsed = .ok ()`;
* `tx2Common inst public_bytes proof checkpoint hash obs = .ok (.Ok ())`.

The operation cut keeps parse, observer marking, and common-call bodies as
explicit slots. The theorem proves the exact emitted wrapper's control-flow
implication for those slots; it does not identify them with source
implementations or discharge D18's full `tx2_common` operation cut.

The generated body at lines 4112–4128 of `source-pins/Funs.lean` is pinned to
SHA-256 `b3aa665deadedac1f04233f5535bce0774cfed34e6ee7f979657982504d97c2b`.
The Rust source at lines 327–331 of `source-pins/candidate-current.rs` is
pinned to SHA-256 `5164975df10f79e9810f9321b8130a9865eb9bb9b6b9de7011f4359ece98c794`.
The Lean wrapper cut keeps the emitted three-phase body in full and represents
the same branch/residual behavior. `check_packet.py` compares the entire Rust
function body and emitted Lean wrapper body (not just ordered tokens), then
compares the complete emitted body against the operation cut using an explicit
callee/type map: `parse_shape`→`parseShape`, `mark`→`mark`,
`tx2_common(inst, …)`→`tx2Common inst …`, generated `verifier.Error`→`Error`,
and the generated ControlFlow namespace→its `Aeneas.Std`-qualified name. The
one syntactic normalization is adding explicit `do` to the `Continue` branch;
that is Lean layout syntax for the emitted monadic sequence. The break arm's
`from_residual` call and all arguments are checked verbatim after whitespace
normalization.

The direct imported `Stage2ContinuationQueryLoop` source and selected object
are recorded in `source-pins/Stage2ContinuationQueryLoop.lean` and
`producer/import-pins.json` (source SHA-256
`c398ba41273939ac739a064eee492976988027ff1b1d6f33657480b17aed0def`, object
SHA-256 `20a8d68464f20012572d37f1228045ac2a42a5776e3d5f8281f7180b24c0d450`).
The selected object was the first matching owner on the captured LEAN_PATH;
this packet does not claim an independent producer receipt for that inherited
owner.

The focused compile used Lean 4.32.0 (compiler SHA-256 and full command/path
are recorded in `producer/receipt.json`). It exited 0 in 12.342 seconds with
peak process RSS 2,242,428,928 bytes, zero swaps, and standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. Earlier failed proof drafts
were superseded during the focused check; only the final source/object receipt
is accepted by this packet.

This is a source-operation cut, not a full caller/source refinement. In
particular, the concrete parser and observer implementations and their source
bindings remain outside this theorem.
