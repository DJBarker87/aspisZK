# V10 factored helper transport

This packet records a kernel-checked all-Result transport for the candidate V10 helper after factoring its emitted head prefix and the exact selected V10 tail cut. `factored_helper_eq_fixed` proves that the V10 result maps through `wideFromEbyK` to the fixed-v6 factored helper result. It composes the green head-value transport with the retained root `v10Tail_to_current` theorem; it adds no independent child-run premise.

The theorem is a source-model transport. It does not establish the Rust `core::array::from_fn` lowering, the full frozen caller/Ops binding, or adoption equivalence by itself. Production sources remain unchanged. The head and tail source cuts and selected object hashes are recorded in `receipts/receipt.json`; the Lean object is intentionally not included.

Validation: `python3 check_packet.py` verifies the packet source hash, receipt schema and retained compile log. Compile was Lean 4.32.0 with `-j1 -M4400`, exit 0, 8.43 s, peak process RSS 3,735,437,312 bytes, swap 0. `#print axioms` returned `[propext, Classical.choice, Quot.sound]`.
