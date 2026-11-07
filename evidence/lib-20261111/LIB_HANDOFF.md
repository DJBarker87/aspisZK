# LIB lane A handoff

Target not yet established; no ledger rows credited. Current assignment is modules 14–18 only, TX1:136/137 library fields. Resumed budget: 250 Lean/link/audit scopes, zero Kani, zero extraction. Earlier notes and the superseded 300-scope assignment are retained in LIB_HISTORICAL_HANDOFF.md.

| Module | Consumer imports | Exact evidence |
|---|---|---|
| 14 VCarriers | LIB_VCarriers, LIB_VEquality, LIB_VReads | Concrete carriers; source-preserving parsed Prefix; native equality and fixed read |
| 15 VField | LIB_VField | Canonical add/mul and mask at same arguments; existing CLOSED arithmetic roots reused |
| 16 VRecords | LIB_VRecordsAll, LIB_VRecordDomains | Getter/payload/state, original decoder offsets, record/frame domains |
| 17 VParse | LIB_VParse | Full parser/transcript/begin result graphs, ordered digest events and functional evaluators |
| 18 VSemantic | LIB_VSemantic | Claims under arbitrary reservation, circle, rounds induction, terminal and caller domains |

Use LIB_FINAL_IMPORT for the focused combined import, including ledger25 NMQ_COMBINED_IMPORT and merged base modules. LIB_STATUS.json lists fields, definitions and supplying laws; LIB_CLOSED.json classifies hypotheses. LIB_CALLER_CLAUSES.json preserves frozen required clauses and adds library-only evidence. Complete TX1:136/137 principal composition remains NNG_/NNH_ work; consumers copy committed files and retained objects, without duplicating proofs.

publicDom remains the frozen hd-only predicate. The asset clause is derived from successful serialization of the SAME Public by LIB_VPublicAsset and LIB_VDomains.finish_of_eval, not assumed by the parent. Canonical output lifts are justified from exact returned native values. Prefix.parse_eq is constructor provenance. No arbitrary Ops, new child-success premise or new trust row was introduced. Existing allocation/Box normalization and runtime digest/reservation trust remain classified, without claiming their removal.

Every host receipt records target, exit, wall time, RSS, swap, revision, source hashes, standard #print axioms, cgroup limits and pinned library objects. Raw ax2 manifests and traces cover only own new roots. LIB_FINAL_AUDIT_SUMMARY.json retains strict collector failures and their disposition under C3-BIN (ab')(3). LIB_EXPORT.json identifies the copy-only retained host objects; LIB_CLOSURE_PINS.json.xz pins selected coherent objects and Aeneas resolution.

No shipped source, frozen spec, trust row, sibling worktree or wallet key was changed. No push. Frozen source comparisons and inherited ELF pins are recorded by final validation. Findings, including the excluded accidental L146 retry and corrected preliminary asset diagnosis, remain in LIB_FINDINGS.md.

Final verification: L178 focused combined import passed; L180 final read raw audit passed; all 190 own roots have standard raw axioms. L158 collector-only diagnostic remains strict exit 1. L181 closure pin/export passed. 88 resumed scopes used of 250; no timeout, OOM, raised cap, Kani or extraction. All five authorized modules are delivered; member-by-member remaining-work disposition is in LIB_REMAINING.md. Host export: /home/dombarker/project-offloads/codex-cx-lib-20261111/LIB_exports_A_20261111. No principal or headline closure claimed.

Raw transcripts with trailing blank lines are preserved byte-for-byte as .log.xz plus uncompressed .log.sha256; no log content was normalized.
