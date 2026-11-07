# NML archive provenance findings

Target not yet established. This is an extraction-input/provenance investigation, not a row closure or security proof. No ledger, trust item or shipped source changed.

## NML-F1: archived LLBC retains missing standalone inputs

The archive scan indexes Git objects rather than sibling worktrees. Producing pin receipts bind exact Rust-source SHA256 values to extraction command arrays. Several standalone `.rs` inputs absent as Git paths are recoverable byte-for-byte from `translated.files[].contents` in the producing job's LLBC. NML_INPUT_MAP.json records the LLBC container Git blob, original file path, embedded SHA256 and computed Rust Git blob. Only the receipt's exact source hash is accepted. Name proximity earns no mapping or reproduction credit.

## NML-F2: complete package recovery is separate from configuration recovery

Archived Cargo package names and lib paths recover additional candidate inputs in the producing packet. They do not establish an extraction configuration. Executable package candidates additionally require archived Charon/Aeneas commands and a command-to-LLBC link: matching output LLBC name, embedded full-source hash and start/include/opaque options. Dependency-bearing references whose complete archived closure is not reconstructed remain unready. A historical --locked command with an unarchived lock remains a visible gap.

## NML-F3: byte differences are not automatically semantic findings

All 17 NMH differences initially remain UNCLASSIFIED. Namespace/import/parameter changes require actual elaboration and equality proof, not textual normalization. Checked versus wrapping arithmetic merits a focused paired-body check on the complete scalar domain; any overflow witness outside canonical M31 must be labelled as such and cannot establish an in-domain caller defect. NML_DIFFS_CLASSIFIED.json retains each original diff hash, candidate and pending obligation.

## Method and exclusions

Only byte identity or the single NHR_parameterize.py discriminant-metadata normalization earns reproduction. Exact declaration segment comparisons are retained even where whole-blob reproduction fails. NMH's conservative lexical CLOSED-row impact is recomputed over remaining non-reproduced blobs; aliases remain conservative, and rootless TX1:059/TX2:040 remain unassessed. No row is reopened here.

The unchanged NHR_stage.py validates the frozen source/graph/lock and tool pins for every extraction. Owned reference manifests/sources are checked independently. Stream A scope count, reservation exit0 + allowed:true, >=40 GB disk and exact 6G/8G/0/64 caps are required before submission. Refusals are waits, never tool launches. NML_ATTEMPTS.jsonl records the waits. No Kani is authorized.
