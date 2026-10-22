# Actual attempt7 `from_le_bytes` map

This source-only proof copies the attempt7 `WideExact.BYTE_LEN` and `WideExact.from_le_bytes` declarations, preserving the original `@[global_simps, irreducible]` annotation on the constant. It proves that the actual extracted byte decoder maps to the retained owned decoder for the same slice. The proof leaves all length checks, ordered byte reads, little-endian lifts, and the final `from_limbs` call in place, then reuses the checked actual `from_limbs` carrier map.

The packet pins the complete generated Funs source and the attempt7 Rust `wide_exact.rs` snapshot. This is a Lean translation-level result about the pinned extracted body; it does not establish compiler binary refinement or deployed runtime behavior. No compiled objects are included.
