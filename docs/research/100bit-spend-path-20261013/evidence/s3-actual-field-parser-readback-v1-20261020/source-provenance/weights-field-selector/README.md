# Frozen field selector: successful decode and canonical outputs

PROVED for the exact unchanged adopted `weights::field` selector: successful execution exposes the checked `i*32`, `i+1` and end-offset operations, the exact selected source slice, and a decoder result `Some value`. Failed decoding cannot become selector success through `Option.unwrap`.

The generated function is elaborated universally over its output type and explicit decoder. Its arithmetic, slicing, decoder call and unwrap body are unchanged; the checker verifies this parameterization and removal of generated resource settings. The selected Rust body is byte-pinned to c8ea8dd49, and the LLBC report confirms the selector body is structured and only the intended decoder is opaque. No unrelated stub body is used as a semantic proof.

Instantiating that function with the retained concrete wide parser and its already-checked component map proves the returned value has canonical limbs. This reuses the preceding concrete decoder theorem; no new field arithmetic or overflow-freedom work is claimed. Correspondence of that retained parser with the deployed decoder, and composition with the full frozen finish/caller, remain OPEN. The packet does not close R14 or R22.

Charon and Aeneas passed in capped NUC scopes; three focused Lean targets passed at -M4400 with 1 GiB high / 2 GiB max / zero swap. The commands, source/import/compiler/object pins, timings, RSS/swap and standard printed theorem axioms are retained. Raw generated Types are uncompiled provenance only; no opaque template axioms, binary, resource-option override or production edit is included.
