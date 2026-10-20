# Fold geometry focused proof packet

See `../../design/FOLD-GEOMETRY-20261020.md` for the theorem map, source
citations, existing pinned extraction results and remaining S7/R14 boundary.

* `manifest.json`: all compile attempts, including failures; command, source
  SHA/revision, direct dependency fingerprint, exit, wall seconds, peak RSS
  **bytes**, swaps, and full output/axiom reports.
* `<module>/<source-sha-prefix>/`: raw command/output/time/receipt. Failed
  attempts may contain error-generated `sorryAx` reports; they are rejected
  and not evidence for any theorem. Only final exit-zero source hashes count.
* `source-pins.json`: new and referenced model/component-source hashes.
* `table-validation.json`: independent arithmetic validation of the 1024
  fast-domain constants, clearly distinguished from formal proof.
* `run.py`: focused compile runner; `check_tables.py`: arithmetic validator.

The accepted `FoldGeometryAudit` root reports every new theorem. The existing
LineFold dependency was compiled unchanged into the private object directory.
No compiled artifacts, binaries or keys are included. The table validation
is a small Python arithmetic check; it is not a heavy elimination/release gate.

One early failed geometry attempt's receipt wrapper observed the shared lock
directory disappear before its final rmdir. The Lean exit, output and time
had already been recorded. That attempt is rejected; the runner now reports
a missing directory without deleting any replacement lock. Successful proof
receipts still require exit zero and standard axioms. The shared mkdir lock
and -M4400 gate are used for all attempts; no other worker's job was killed.
