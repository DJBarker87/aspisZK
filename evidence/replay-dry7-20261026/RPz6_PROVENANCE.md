# Producer provenance gate

The larger cohort is the complete **historical e5c186ba3 Tx1 cut**, not an
unqualified extraction of the whole frozen D188 source. This distinction is
material. Its original archive's raw Types SHA256 is
`bb4ccfd7a77b6e45de16181113c888febda2ecf8c23bdad55c1919fe92762c3e`;
raw Funs is `f4aee2661033aeaf820623a7decb3687e2617ae50a2ad4b41e78b253025a1de1`.
These exactly match union-pins.json / tx1-binding-pins.json. The archive's
source-pins revision is e5c186ba3bcbbf9a0cc5878077aa8848853a65cc;
root crate::verifier::tx1, with explicit opaque child boundaries. Its phase
cut is verifier.rs bytes [1082,1275), SHA256
`9b0869f89f920e2deedb314de8300894b0e53be65a54c3202367d508c6348c85`.
The union retains Prepared carriers and appends five Tx1 carriers, including
verifier.Phase. Historical objects e1d3e2db… / 06348080… are not source hashes.
The current named-discriminant Types source is b45ee735…; RPz5_057 binds that
source to its fresh object. RPz5_058 uses the prepared Funs 544b75b9… (not a
byte-identical historical 06348080… object); the latter's body provenance is
recorded separately. This is a retained adapter/union, not raw generator output.

The smaller Types/Funs sources 0514a63e… / 544b75b9… are the later naming-adapted
Prepared-only cohort. Its naming-adapter records Prepared source 69f3ab1c…;
it does not provide the five Tx1 carriers. It cannot be the complete Tx1 cut.

The explicit comparison scans all 285 JSON/Lean/Markdown files under
lean-candidates/*/extraction/**: none is byte-identical to either selected
producer or the historical raw Tx1 Types/Funs, and none literally names their
full digests. All JSON inventory hashes and exact comparisons are retained in
RPz6_PROVENANCE.json. Absence here is not evidence against the separate
historical Tx1 archive, whose raw output hashes match positively.

D188's actual AeneasExtraction structure names stage1_owned, stage2_owned and
digestSource; it does not name either PublicPreparation producer or a source
revision. Its digest-source-reuse.json explicitly reuses only unchanged
three-line digest syntax, excludes the failed current-root Charon004, and
retains the source interpretation as a premise. Thus the supplied evidence
supports selecting the larger carrier for the historical Tx1 consumer, but
**does not establish either producer as a complete extraction of the frozen
D188 implementation**. No historical proof is reassigned to a new frozen pin.

Next gate: inspect both Phase constants in the existing larger-cohort view
and kernel-check the requested type equality, without editing any consumer.
No premise removed; no source-to-ELF claim. No shipped source changed.
