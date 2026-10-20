# S4 four-dots fixed-call candidate v2

This packet adds an actual generated-helper call theorem to the isolated v6 extraction candidate. It does not modify the committed v1 packet or production Rust. The Rust candidate replaces `array::from_fn` with explicit calls and expands the fixed-size loops; equivalence to the original `from_fn` behavior remains open.

`FunsOpsFixedV6.lean` is a six-definition adaptation of the exact generated Funs source. The mechanical checker verifies the complete transformed source against the stored adapted file, preserves each declaration body, threads one `FourDotsOps` value through the helper calls, substitutes only the listed external operation calls with explicit record fields, and rejects external template imports or resource-option overrides. The adapted owner uses the exact same nominal `FourDotsOps` and generated types from the pinned `FunsOpsV4`/`Types` owners.

`fixed_success_calls_actual_helpers` proves that success of the adapted fixed wrapper entails successful execution of its actual emitted `four_dots_one` helper at slots 0, 1, 2, and 3, in order, with the same output array and the same converted 608-byte input. The operation implementations remain explicit fields of `FourDotsOps`; this theorem does not assume helper success or discharge the arithmetic semantics of those operations.

The Lean consumer is standard-axioms clean: `[propext, Classical.choice, Quot.sound]`. The older failed/stale Formatter and `sorryAx` attempts are not selected; this packet pins the repaired Formatter/Aeneas object overlay and coherent S4 Types/FunsOpsV4 owner. See `evidence/dependencies/selected-imports.json` and the phase receipts for exact pins.

Still open: original Rust `array::from_fn` equivalence/adoption; concrete arithmetic of this helper against the seven-batch bound; composing the same helper with caller `g` coordinates; production-source adoption.
