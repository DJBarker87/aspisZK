# S3/S9 generated helper with explicit P6 operation slots

This packet records a focused, axiom-audited Lean compilation of the generated
`kpowers`, `scalar_factor`, and `factored_s2_libra_weights` definitions. The
generated helper control bodies are retained by the source checker. Six field
operations are explicit `FieldOps` projections; their field laws are not
proved here. The generated FnOnce/FnMut callback adapters and array materializer
are connected to the reviewed P6 model interface, but this packet does not
prove those adapters equivalent to the original Rust standard-library
execution.

`#print axioms` was run for `kpowers`, `scalar_factor`, the factored loop body,
the loop, and the wrapper. Each reports only Lean's standard `[propext,
Classical.choice, Quot.sound]`. The source contains no `sorry`, `admit`, or
custom `axiom` declarations.

This is a generated-helper/P6 candidate result. It does not prove the enclosing
frozen `Weights::pair` caller, source equivalence of a helper normalization,
field-operation refinement, or the Rust `from_fn`/fold correspondence. The
source/body adapter obligations remain explicit for the next consumer proof.

Run `python3 check_packet.py` from the repository root to validate source and
evidence hashes plus the adapter checker. No `.olean` or other binary is
included in this packet.
