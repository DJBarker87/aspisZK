# R442–R445 finite rejection evidence

This bundle contains the byte-identical promoted sources for R442, R443, and R445; the direct R421 source import for R442; complete successful and failed run source/log/receipt triples; and the focused runner. Exact targets, hashes, revisions, limits, metrics, and axiom reports are in `manifest.json`.

Run `python3 verify_evidence.py` from this directory for a read-only integrity check. The failed drafts are explicitly marked rejected. `sorryAx` appearing in those rejected logs is not part of the successful proofs.

The formal boundary is a finite uniform option tape and the initial block’s modeled eight-word rejection distribution. It does not establish source sampler execution, shared-oracle IID behavior, or challenge freshness.
