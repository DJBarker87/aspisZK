# Shared-environment replay failure

NDJ_R001 failed at IMPORT, exit 1, wall 4.690684114932083 s,
peak RSS 5384088 KiB, swap 0; source revision da54a9c439.
Full source, selected object pins and exact command are retained in its receipt.
No #print axioms ran. No memory failure or cap increase occurred.

`ExtractedDigest32Transcript` and `RPz7_ExtractedDigest32Transcript` both export
`AspisR1PublicPreparation.TranscriptStep.readParts`. The pinned headline replay
renames modules; the joint fixture uses historical module names. The two
closures cannot be imported together unchanged. A larger cap cannot fix this.
No unchanged rerun of this combined source is authorized or performed.

Replacement: separate root audits in the same task-owned pinned workspace,
preserving the predecessor's exact selected objects for each root. The combined
closure is reported as a union of two forests, never as a single shared Lean
environment or a fresh joint instantiation of the headline. This supplies root
statements/axioms and dependency inventories; the shared-cohort reconciliation
remains an L188 finding. It requires module-name/producer reconciliation and a
new explicitly scoped replay, not additional trust or an invented discharge.
The single final replay requested by the lead therefore has no successful
shared-environment result in this packet. Final manifest must retain that limit.
