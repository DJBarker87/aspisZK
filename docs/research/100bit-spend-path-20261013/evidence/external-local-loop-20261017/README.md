# Actual external-linear first loop

`PoseidonExternalLoopFuel` proves execution and the exact local four-by-four matrix model for the complete first loop of extracted `external_linear_lazy`. The symbolic fuel invariant preserves untouched groups and replaces each processed group with its mathematical matrix image. The frame lemmas derive behavior of all actual writes rather than assuming a source update model. `PoseidonExternalLoopCanonical` proves canonicality of the whole intermediate state, reusing actual canonical row outputs and checked updates.

These results reuse the already committed source group body, loop step, field model and row/reducer proofs. They cover the first loop only. The complete external-linear wrapper also constructs four column totals and adds those totals to all sixteen lanes; those callbacks, reconstruction and final loop remain the immediate continuation. The local matrix result is not claimed to equal the complete external-linear model.

Two cached objects were admitted under their namespace-prefixed import paths without recompilation; `object-aliases.json` records the compiled module, admitted import and exact unchanged object/source hashes. Their consuming targets passed against these exact pins. The maintained source is placed at the admitted import path; no second copy of the same declarations is introduced at an unprefixed path.

Production Rust and runtime artifacts are unchanged by this proof packet. The full oracle/source, authenticated persistence/custody/runtime, sampler and final soundness/privacy instantiations remain open. This is not the complete 100-bit security theorem.

Validation: 6 focused targets; 7 standard-only axiom reports; zero process swap. Maximum RSS 4,079,096 KiB. Receipts record exact source/object/import hashes, command, base revision, wall time, RSS and cgroup cap. Repeated and internal import pins were checked for coherence. No unchanged full replay was run. Assembly parent: `7666f3710eed04b31dc714d63a07e9e4d2eecea4`.
