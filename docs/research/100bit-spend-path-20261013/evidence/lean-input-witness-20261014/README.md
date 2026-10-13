# Input-witness Lean evidence

This bundle contains five focused successful target attempts at source base `df240a6cda47343b7e50bd4f7e4900ea6f431f65`; no failed attempts were present in this bounded batch. Each target retains its NUC receipt, stdout log, time log, SHA256 sidecar, and hash-matched source snapshot. Final object member hashes are in `source-manifest.json`; objects are retained only in the normalized `final-objects.tar.gz` archive.

The added public theorem `R0P.input_note_trace_witness` was compiled from the `R0P/Extraction` overlay. `prestate/` retains the original source, compiled source, restoration note, and the old `R0P/Extraction.olean` in its separate `prestate-object.tar.gz` archive. The worker note records that removing exactly the added theorem block and its `#print axioms` line restores the source byte-for-byte to the HEAD version; root will independently verify this comparison. The original `.olean` is not included as a loose file.

Pinned runner/environment snapshots are under `environment/`. No build was run during this evidence collection, and this bundle makes no security-closure claim.
