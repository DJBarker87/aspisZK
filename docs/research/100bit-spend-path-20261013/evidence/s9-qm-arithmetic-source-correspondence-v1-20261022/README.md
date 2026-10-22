# QM31 arithmetic source-correspondence packet

This packet records the exact source and retained Lean/extraction pins for `QM31.mul` and `QM31.square`. It does not rebuild Lean or Rust and makes no ELF, runtime, or production-caller refinement claim.

The six pins are the five cut-input files in the source-cut identity manifest plus its `src/field.rs`: Cargo.toml, Cargo.lock, lib.rs, weights.rs, transport.rs, and field.rs. The checker also verifies that the saved method texts hash to the recorded method-body digests and occur in the pinned field.rs snapshot and current worktree.

For multiplication, the concrete `FieldOps.qmMul` slot is inherited definitionally from `currentQMOps`; there is no `actualQMMul` implementation in `S3S9ConcreteFieldOpsV1`. The current-wide Aeneas translation maps the exact `field.rs` span to `AspisR1CurrentWide.field.QM31.mul`, and retained bridge/semantic theorems establish operation correspondence and exact decoded multiplication semantics.

For square, `concreteFieldOps.qmSquare` dispatches to `actualQMSquare`, which calls the selected-mask Aeneas translation of the same exact source span. The retained `current_qm_square_exact` and `concrete_qmSquare_total` theorems supply the square semantics.

`r0-op-count` is not enabled by the pinned extraction invocation or Lean operation model. The `#[cfg(feature = "r0-op-count")]` lines are nevertheless included in the pinned method bodies; this packet does not make claims about builds that enable that feature.

Run `python3 check_packet.py` from this directory to check all listed source hashes and external owner-object path/hash pins.
