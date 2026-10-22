# Strict parser success to candidate `checked_q` child

The Lean source proves the candidate `Q.from_limbs` behavior on the exact source-order coordinates projected by `limbs_of(k)`: `[k.c0.a,k.c0.b,k.c1.a,k.c1.b]`. Four coordinate bounds imply the child returns the same four-word array, and the current strict parser's successful result supplies those bounds for the same `CurrentQM` value. The theorem `parser_success_checked_q_coordinates` therefore identifies candidate output coordinates with the strict-parser result coordinates.

The frozen Rust source confirms `checked_q(k) = canonical::Q::from_limbs(limbs_of(k)).ok_or(())`. The trivial outer conversion and full push-to-QRaw binding are covered by the stronger committed `evidence/s4-checked-q-push-bridge-v1-20261021` owner; this packet does not claim the full S4 or caller cone is closed.

Focused run: Lean 4.32.0, exit 0, 9.756406 seconds, 3,267,969,024 bytes maximum RSS, 0 swaps, standard axioms only. The launch revision was recovered from the reflog and object mtime rather than directly captured; exact source and dependency source/object hashes are pinned.
