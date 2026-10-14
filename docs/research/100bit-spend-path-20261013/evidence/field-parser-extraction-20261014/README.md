# Field parser extraction provenance

This bundle preserves three focused Charon/Aeneas extraction attempts. Compiler target/cache files are excluded. Original runner scripts, copied source, lockfiles, LLBC, generated Lean/templates, commands, environment/tool pins, logs, and timing files are members of `field-parser-extraction-attempts.tar.gz`; `manifest.json` hashes every member. Outer orchestration tool results are retained under `tool-results/`.

- `a`: Aeneas completed, but standard helper templates remain opaque; translation is not Lean-checked.
- `b`: Aeneas failed with `Inconsistent state` at `core/result.rs:713-717`; the failure is retained.
- `c`: the M31-only target translated successfully without the helper closure; it is not Lean-checked.

This records extraction artifacts and failures only. It makes no source-security claim.
