# Reseed-edge focused Lean evidence

This bundle records 34 capped focused attempts against source base `1268803b1b3ecab9120af3d32356542116dcf9a9`: 24 failed attempts, nine final successful targets, and one successful but superseded wrong-module-path attempt. Every attempt snapshot was checked against its receipt and SHA sidecar; all receipts, stdout logs, resource time logs, and snapshots are retained.

The earlier `TrailingStateFrame-a..g` attempts used module path `TrailingStateFrame`; the corrected final target is `R1TrailingStateFrame-a`. The superseded `TrailingStateFrame-g` green result is retained as historical evidence and is not counted as a final target.

The `R1ReseedCheckpoint-a` final source hash is `61aed9076a02da2978d6385071eef1dc7e1c11ceb3cc9dbda019e59afdb40d74`; it completed in 1.42s at 3,526,844 KiB peak RSS with zero swap and 25 axiom reports.

`objects/reseed-edge-objects.tar.gz` contains exactly the nine final Lean objects with normalized metadata. `frame-source-check.json` and `runtime-source-check.json` were supplied separately and preserved unchanged. This bundle records focused proof build evidence and source fingerprints; it makes no protocol security claim.

`SHA256SUMS` covers every bundle file except itself.

The independent lead audit in `ROOT-VALIDATION.json` verifies all 34
attempt snapshots against their receipts/sidecars, every resource receipt
against its time log, all nine current sources and archived objects, and
all 51 successful axiom reports (48 final, three superseded). Only standard
axioms occur. The literal P3 bytes and all 14 runtime fingerprints were
also independently rechecked; no runtime or protocol-security conclusion
is inferred from those source comparisons.
