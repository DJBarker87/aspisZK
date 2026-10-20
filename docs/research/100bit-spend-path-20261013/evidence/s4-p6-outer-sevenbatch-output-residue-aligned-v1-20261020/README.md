# S4 P6 aligned N8 residues

This theorem composes the aligned four outer callback outputs with the exact N8 reducer arrays from those same callback witnesses. For each successful returned N8 array, it retains the eight actual limb reads and reducer successes, proves the returned words equal the corresponding limb residues modulo P, and proves all returned words canonical. It uses the accepted `ActualM31OpsBinding.reducer_success_mod` on those same reducer results.

This is a source-model theorem. Rust `array::from_fn`/P6 correspondence, complete frozen caller reachability, and coordinate/caller hypotheses remain open. No production equivalence is claimed.

Run `python3 check_packet.py` to verify the inventory and source hashes. Compiled objects are excluded.
