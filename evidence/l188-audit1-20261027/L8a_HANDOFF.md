# L188 audit handoff and closure ruling

**Audit delivered with findings. The deployed 100-bit target is not established.** Branch `codex/cx-l188-audit1-20261027`; local stage commits, no push or merge. No shipped source, harness, original/session A candidate, ledger, contract, key or wallet changed.

## Recommended ruling for this cohort

| Gate | Ruling-ready result | Exact remaining limit |
|---|---|---|
| L187: coherent repository replay | **Eligible to close for the selected RPz8 cohort only.** Rc10 has 4,963 green repository modules; ARX has 5,259; union 5,260, no unbuilt/failed/unresolved source vertices. Reuse RPz8 receipts rather than repeat the unchanged package. | This is not an unqualified frozen-release source certificate. D188 producer/release association remains open; the historical cached top's missing CircleSampleWrapper object still prevents its historical/fresh kernel byte comparison. ARX is a candidate, not adopted. |
| L188: final axioms/trust release gate | **Do not mark unconditionally closed.** The complete kernel/import trust census and exact named-field reconciliation are now delivered, including clean AuditRoot prints. | F-AXIOM: imported all-declaration standard-only fails (105 nonstandard import-only axioms, none top-reachable); F-CONTRACT: accepted trust rulings are not a complete named inventory in SECURITY-CONTRACT; W1 copy domain and D188-P producer provenance remain explicit. The lead must resolve the acceptance of the scoped import/library findings and the release pin association, rather than hide them behind clean headline summaries. |
| D188 producer provenance | **Finding; not closed.** Coherent selected producer is an adapted historical e5c/Prepared union, not the byte-identical raw extraction of the H5 release pin. | Original pinned extractor and LLBC paths absent on host; no substitute tool/source launched. Eight of thirty original e5c cuts are absent verbatim at the H5 release input. No semantic inequivalence or attack inferred from source-byte differences. |
| Joint deployment non-vacuity | **Separate, open.** No new simultaneous inhabitant of all Rc10/ARX hypotheses. | RPz8's FIn/FIo conditional witnesses and Parsed Phase witness retain their success/installation/primitive conditions and their original scope; they do not supply the joint deployed fixture. |

These are recommendations, not ledger edits or release adoption. No numerical premise-removal credit is taken for completing an audit or recommending a cohort-scoped replay gate.

## Exact pins and outputs

The coherent host workspace is `/home/dombarker/project-offloads/codex-cx-replay-dry-20261026`, with unchanged ordered roots: Lean toolchain library, RPz8_overlay, RPz7_overlay, RPz4_trusted, RPz_trusted. Lean is 4.32.0. The pinned roots are:

- `RPz8_Rc10_Top.olean`: `e41293c79dfe185dd7e3489b9d4cad8150d3dc28b31eebdf30d9c4a2f52fc181`, 218,920 bytes.
- `RPz8_ARX_Root.olean`: `e627f8a415ab48b344731be2aa33c51ae0686b42fc72438e1e7680d8e0e3002a`, 242,784 bytes.
- `Aeneas.Std.Core.Fmt.olean`: `63b8efa3940faa81bb26f1b6ea140b2d6b81c1f1155b3fafa0544f6e1e82b9fc`, 237,376 bytes.

`L8a_HostPins.json` also pins the fresh producer Types/Funs objects and both missing historical extraction paths. `L8a_CohortReceipts.json` hashes the exact reused RPz8 frontier, final validation, selected source, formatter, non-vacuity and statement-comparison receipts. No old object/source hash is silently renamed as a new one.

Deliverables:

- `L8a_TrustAudit.md`: complete 108-name axiom list and every opaque/implemented_by/extern/partial declaration (9,224 union surface records); all 44 fields of the 12 named trust/historical records plus the definition-valued RuntimePersistence law; one-to-one field map and exact contract gaps. The union inventory covers 630,972 constants and 4,909 structures. Exact raw types and metadata are in L8a_007/stdout.log and L8a_008/stdout.log.
- `L8a_ProducerProvenance.md`, `L8a_ProducerComparison.json`, `L8a_ReleaseCutComparison.json`: selected versus raw/manifest/release pins and the bounded extraction-check result.
- `L8a_AuditRoot.lean`: fresh Rc10 and ARX imports with both #print axioms receipts, L8a_006.
- `L8a_StatementComparison.json`, `L8a_Rc10_Top.BEFORE.statement.txt` / `.AFTER.statement.txt`, and the corresponding ARX pair: complete universe and kernel Expr representations. The canonical BEFORE/AFTER files are byte-identical for each root; their Expr strings equal RPz8's complete fresh statements. No comparison to the unavailable historical cached root is asserted.

## Actual-top before/after, ledger method and non-vacuity

Before and after are the same fresh `AspisR1.Rc10_Top.deployed` statement; ARX is separately unchanged. Every binder, quantifier, carrier, failure event, conclusion, game clause, probability metric and trust record is identical. No wrapper theorem is substituted to claim progress. Premises removed/added/changed **0/0/0**. Recount method: actual plus deployment, split quantified atomic families, preserve shared witnesses, deduplicate L185=L159 and existing aliases, preserve T/P/G/C classification. Delta **T0/P0/G0/C0**. The old 83T/12P/13G actual and 89T/16P/13G deployment-inclusive figures are historical Rc10 counts, not a newly established absolute ARX recount. No ledger row was edited or credited.

A clean axiom list is not proof that trusted runtime/source premises have an actual joint instance. No joint non-vacuity is added; no source-refinement gap becomes cryptographic trust. Frozen3, the approved two-transaction game and data-only RuntimePersistence remain unchanged.

## Executed validation and AGENTS receipt fields

Six Lean compiler invocations used of 100 (IDs L8a_003–008); two earlier IDs are preflight-only rejections before Lean. Three clean passes, two elaboration errors and one diagnostic exit-zero run with name-API panics (not counted as a clean audit). One capped Python extraction checker passes; zero Kani, Rust builds or SBF builds. No timeout, memory kill, cap increase, unchanged failed compiler rerun, unchanged package regression or reservation retry.

Each scope: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Lean `lake env lean -j1 -M7000 -DElab.async=false`, one module per attempt, one scope at a time. All attempts' source revision is `4c9cee7a2a` with exact dirty-source hashes and selected direct dependency hashes in each receipt. No new top theorem was added; #print axioms is recorded for both audited deployed theorems and every printed trust definition/record.

| Attempt / exact target | Exit | Wall seconds | Peak RSS KiB | Swaps | Axioms / status |
|---|---:|---:|---:|---:|---|
| L8a_003 / `L8a_AuditRoot` | 1 | 3.585077182 | 5543752 | 0 | diagnostic; retained errors/panics |
| L8a_004 / `L8a_AuditRoot` | 1 | 2.568282567 | 5545468 | 0 | diagnostic; retained errors/panics |
| L8a_005 / `L8a_AuditRoot` | 0 | 71.401059304 | 5977844 | 0 | diagnostic; retained errors/panics |
| L8a_006 / `L8a_AuditRoot` | 0 | 2.533903304 | 5542644 | 0 | standard-only deployed roots |
| L8a_007 / `L8a_SurfaceInventory` | 0 | 27.665560264 | 5977632 | 0 | standard-only deployed roots |
| L8a_008 / `L8a_TrustFields` | 0 | 2.923374589 | 5563452 | 0 | standard-only printed trust definitions/records |
| L8a_Check001 / `L8a_retained_extraction_check` | 0 | 0.044612718 | 18984 | 0 | N/A: extraction checker |

Aggregate scoped command wall: 110.721869928 seconds; maximum peak RSS: 5,977,844 KiB; swaps zero. Original full stdout/time/config/receipt files are retained, including diagnostic failures. `L8a_FinalVerification.json` checks all source hashes, exact caps, clean-query completion, kernel statements and cleanup. Raw launcher captures and the literal git source diff retain original trailing whitespace, so a repository-wide diff whitespace check reports those raw-evidence lines; authored code/prose checks exclude only these explicitly retained raw files.

The 94 unused Lean attempts are not exhaustion. Every requested fresh kernel/field inventory target is complete; the remaining producer reproduction is blocked before launch by missing pinned extraction inputs/tool. Repeating unchanged imports cannot resolve that provenance finding and would violate the no-unchanged-regression rule. No infrastructure/toolchain repair is attempted under local-lean rule 5.

Own query .olean scratch and the small extraction-check symlink layout were removed after recording SHA-256 and sizes in `L8a_cleanup.json`. Coherent shared source proof objects remain intact for other workers. No binaries, tarballs, objects or ELFs enter commits.

The ELF rebuild trigger did not fire. Historical release pins (not rebuilt here): default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`; devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`; Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`. Their S10 compiler-input pin is `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.

Next deliverable: a lead ruling on the named import/library/contract reconciliation findings, and exact D188 producer-to-release association using pinned extraction tools or an explicitly adopted certified producer. Joint non-vacuity remains an independent gate. The release target remains not established.
