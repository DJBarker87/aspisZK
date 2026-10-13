# Focused query-chain checks

Run `python3 validate_manifest.py` from any directory to check the exact source
hashes, successful receipts, timing logs, cap settings, zero swap and every
printed axiom list named in each selected source. The parser includes wrapped
axiom output. Scope and remaining obligations are in `../../QUERY-BINDING.md`.

Base revision: `3638d7546f6e03a1afb0eaabdb1cff38d1631e84`; dirty source hashes
are authoritative for these focused checks. Lean is 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. The pinned NUC runner and its
4G high / 6G max / zero-swap limits are documented in the manifest and prior
concrete-extraction evidence. No full release replay is asserted.

`R1RhoAcceptance-a` was a failed source-staging preflight: the requested local
patch was not present, the copy failed, and the remote source was absent.
The runner wrote a missing-file log, an empty SHA sidecar and timing output;
no compile receipt could be generated. Those raw outputs are retained. After
writing and checking the source, attempt b compiled successfully. This was not
a theorem failure or a memory-cap failure.

The query-law import dependency bundle is adjacent in
`../lean-query-imports-20261013/`. The root independently compared all eight
changed historical Lean files against the base: only import lines changed.
That comparison is recorded in `root-import-review.json`.
