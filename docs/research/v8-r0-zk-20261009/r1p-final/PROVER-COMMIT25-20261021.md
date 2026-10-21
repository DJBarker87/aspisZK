# Prover commitment part 25

Base `87684ed0d`; branch `codex/cx-prover-commit25-20261021`.

Target not yet established. Updated incrementally after each verified stage.
No tracked shipped file or concurrent-owned module is changed.
The final user-assigned Env J range 7500–7699 is used, after checking receipts.

## Stage 1 — owned add-small reference

Kani `iterator_equals_indexed` proves the shipped iterator body equals the
retained extracted indexed reference: same boolean and every final digit,
for all canonical eight-digit arrays and all addends ≤257. These are the
existing arithmetic theorem's domain and cover both gamma increments.
Both function bodies are copied mechanically from their pinned inputs;
only visibility and module names differ. No production source changed.

The successful v3 gate has exit 0, wall 1.087 s, peak RSS 159892 KiB, swaps 0,
6G/8G/no swap/64-task scope, and exact pins in `addsmall-source-pins.json`.
No Lean compilation is involved in this Rust gate (`#print axioms`: N/A).
P6 remains the explicit Kani/Aeneas translation trust boundary.

v1 is a rejected CLI invocation (missing `-Z unstable-options`). v2 is an
excluded unwind failure in the implicit 32-byte memcmp used by array equality;
v3 checks all eight scalar equalities instead, retaining unwinding assertions.
The source loops and bound remain unchanged. All three receipts are retained.
This closes the source equality for the owned add-small reference; it does
not by itself identify every caller or install the complete scalar policies.

## Product coupling and endpoint

Not yet constructed. No refinement premise has been deleted.
