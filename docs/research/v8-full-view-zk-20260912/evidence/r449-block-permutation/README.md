# R449 block-permutation component evidence

The promoted R449 source is byte-identical to the successful input saved in `run/source.lean`. The exact Lean command, launch record, raw GNU time output, environment snapshots, log, receipt, and runner are retained in this component. `manifest.json` records the compiler result, full axiom output, direct import hashes, and resource limits.

R449 proves permutation-equivariance for the abstract bounded rejection scan and preservation of the sentinel under the induced masked-word permutation. This component is being held for the joint R450/R451 source-coupling milestone; it does not claim shared-oracle freshness or a complete four-limb distribution.

The direct R445 and R446 dependency sources are referenced from the existing [R447 evidence bundle](../r447-source-initial-block-law/README.md), rather than duplicated here. The verifier checks those saved copies and the current promoted sources against the hashes in this manifest.

Run `python3 verify_evidence.py` from this directory for a read-only integrity check. No compiler rerun was performed.
