# Final installed QM31 parser to accepted V10 carrier

This focused Lean target follows the parser slot through the final `FourCallbacksForward.install` record. It proves that the literal V10 helper's `literalQMFromBytes` result equals the transparent generated DecodeK `QM31.from_le_bytes` result mapped through the Current parser carrier and then `qm31FromEbyK` into the accepted V10 QM carrier. The equality covers every slice, `Result` branch, and `Option` branch; it does not assume successful parsing.

The proof reuses the exact prior all-outcome installed parser theorem and `tail_install_fixed`/record reduction, rather than assuming a parser-slot binding. It uses only `[propext, Classical.choice, Quot.sound]`. The monitored Lean 4.32 run exited 0 in 20.328s, peak aggregate RSS 3,716,988,928 bytes, process RSS 3,726,426,112 bytes, zero swaps.

Two changed failed attempts are retained under `evidence/diagnostics/`; neither is represented as accepted evidence. The target does not equate the parser with the separate axiom-bearing V10 `FunsExternal` declaration and does not close Rust standard-library correspondence or the full S4 re-pin. Run `python3 check_packet.py` to verify retained evidence pins.
