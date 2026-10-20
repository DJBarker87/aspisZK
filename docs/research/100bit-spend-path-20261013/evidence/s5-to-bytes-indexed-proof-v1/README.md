# Indexed-store `WideExact::to_le_bytes` candidate proof

This packet records a focused Lean proof for the extracted indexed-store candidate. It proves that the candidate function succeeds and returns the exact 32-byte array represented as eight ordered four-byte `U32.toLEBytes` groups, corresponding to `WideExact::to_limbs` in order. The array subtype records length 32; the proof avoids evaluating a flattened large numeral.

The source candidate changes only `WideExact::to_le_bytes`: it converts eight limbs and performs 32 constant-index stores. `check-packet.py` verifies that exact method-only diff against the pinned original and that the Lean source adapter is the generated Funs source with only the two Aeneas resource-option lines removed. The generated external template is not imported. The accepted theorem's axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.

This is an isolated candidate. It does not prove equivalence to the original `chunks_exact_mut`/`zip`/`copy_from_slice` method, and it does not establish that the Rust standard-library mutable chunk iterator has the candidate's semantics. Production source remains unchanged.

The candidate extraction LLBC SHA-256 is `0e5a00bd36f1d6aeba70326a72720e3492c77dd80886209b0eebd3d0ed23a6e2`. Charon and Aeneas succeeded under separate 2 GiB high / 4 GiB max / 0 swap scopes. Their detailed receipts and source pins remain in `../s5-to-bytes-indexed-candidate-v2/`.
