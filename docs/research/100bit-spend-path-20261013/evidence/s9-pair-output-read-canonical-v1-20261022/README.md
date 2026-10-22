# Pair public output read canonicality

This packet proves a projection-ready contract: from the same successful Pair public helper result and its mapped-input canonical-read contracts, every successful dynamic index read `output[idx] = coef` yields canonicality of the corresponding `Pair.toP6W coef`. The proof derives the `< 4` bound from the successful array read, maps that exact read through Pair→Candidate→P6, and identifies it with the public theorem’s canonical `Fin 4` output cell.

No output-canonicality premise is assumed. The packet records the exact source/profile/import pin and standard-only axiom report, and contains no compiled object. This is a selected-model result, not production Rust identity or binary refinement. Run `python3 check_packet.py` to verify the packet.
