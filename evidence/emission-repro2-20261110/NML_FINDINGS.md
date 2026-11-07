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

## NML-F4: E001 restart violated the share recheck interval

NML_ADMISSION_FINDING.json records a 15.095-second recheck after the last >=2 refusal, caused by the owned receipt-context repair restarting its local waiter. Actual prelaunch count, reservation, caps and disk passed, but the required 180-second wait did not. E001 earns no provenance credit and its Charon/Aeneas charges remain. The owned client now preserves the deadline across restarts. No unchanged rerun was made. This finding does not affect the independently admitted NML_L001 arithmetic check.

## NML-F5: two compared total scalar bodies are semantically different

NML_L001 passed on NML_DiffArithmetic.lean: exit0, wall3.148678s, peakRSS2602496KiB, swaps0; exact revision/source/dependency hashes are retained in its receipt. All five printed theorems use only [propext, Classical.choice, Quot.sound]. NML_Diffs.body_difference0 and body_difference1 compare the exact field.M31.add body segments of the two NFG inverse blobs against NMH_E008's emitted definition. At U32 inputs (4294967295,1), checked addition fails integerOverflow and wrapping addition returns ok0. This establishes DIFFERS_SEMANTIC for these total scalar functions. The witness is outside canonical M31; it proves no canonical-domain caller or native security defect, closes no row, and does not alter trust. The remaining 15 original NMH differences remain UNCLASSIFIED.

## NML-F6: a frozen-crate opacity metadata assumption blocks a reference crate

E009's optimized pinned Charon exits0 and produces retained LLBC a51f34b8e0d4a0e13b485b32c518daf8ac4a6e97006a8be0ee11ecf04cdba0ff. NHR then refuses the archived crate-local opacity path because its default expansion names aspis_r1_cost_probe rather than eby_k_push_cut. No Aeneas ran in E009. The owned adapter supplies the actual reference-crate selector and retains all hit/opaque checks; NML_A001 is a separately admitted first Aeneas attempt over the unchanged successful LLBC, with explicit zero-charge Charon reuse. Original failure and command receipts are retained.
