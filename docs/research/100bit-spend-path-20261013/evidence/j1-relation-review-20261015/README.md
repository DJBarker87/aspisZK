# J1 relation evidence review

This is a read-only audit of eight named Lean modules and their existing evidence bundles. No compiler or test was run and no source or bundle was changed during the audit, except that the two immediately preceding task-owned SpendRelation manifests now explicitly index their object archives and have refreshed checksum lists.

For all eight targets, the current local source matched the green receipt source hash; the green receipt reported exit status 0; the preserved green source snapshot matched that hash; and the bundle `SHA256SUMS` checked successfully. The final object archive and declared member hashes were checked. The compiler output contained every source `#print axioms` directive; the per-theorem reports and aggregate observed axiom names are recorded in `review.json`, alongside attempt time, peak RSS, swap, cgroup, source revision, and import provenance.

Two bundles were compiled from source revision `8e6c2b4cba1c54fe165f7436f5fc3ada1e1ae0f3` (`R1RecoveredC2Semantic`, `R1CanonicalC2SemanticOpening`); the other six record `57edab99fe104f23b3d3c881d1e87c1abb0975c0`. This records provenance only. The `R1SemanticPayloadView` bundle pins object hashes for `R1SemanticRecordCodec` and `R0P.MaskView`, but does not include their source hashes; that source-provenance gap is called out in the JSON. The other bundles provide direct import source/object pins or, for `PublicOptionShape`, record the cached `R0P.Core` object and distinguish it from the included repository source snapshot.

This review checks artifact consistency and printed axioms, not theorem adequacy, cryptographic closure, or source correspondence.
