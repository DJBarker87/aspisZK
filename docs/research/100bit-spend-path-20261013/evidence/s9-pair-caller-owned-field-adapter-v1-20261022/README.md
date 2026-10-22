# S9 pair caller adapter backed by the owned field reader

This source-only focused proof packet records a green `pair_field_success_actual_reader` theorem. The pair adapter's `weights.field` slot calls the selected owned extracted `AspisR1S9FieldOwnedV1.weights.field` body and maps only the returned nested record into the pair carrier. The theorem derives the same call's selected slice, arithmetic witnesses, parser byte readback, limb bounds, and selected-carrier canonicality.

The bridge target has an explicit `#print axioms` report in its Lean log: `[propext, Classical.choice, Quot.sound]`. `Types`, `FunsExternal`, and `Funs` are retained as exact compiled dependencies for this theorem; this packet makes no separate axiom claim for those declarations. Their source hashes, successful compile receipts, profiles, commands, preflights, and controller hash are pinned. No unchanged Lean targets were recompiled while packaging this packet.

The packet establishes an adapter/model correspondence. It does not establish that the owned Lean extraction is the frozen production Rust caller body, nor that source/runtime checked-index semantics match the model. The 90-byte Rust body/source-cut identity and checked-index bridge remain separate open obligations. No production code was changed or adopted.

Compiled `.olean` and other binary artifacts are intentionally excluded. `check_packet.py` verifies source/receipt/preflight/profile/controller/direct-import pins, checks the bridge theorem's axiom report, labels other modules compile-only, validates linked packets, and rejects compiled artifacts.
