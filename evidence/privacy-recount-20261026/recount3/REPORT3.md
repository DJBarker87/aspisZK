# Recount 3 final report

Branch: codex/pv-recount3-20261027. Base: 0f950391c824a835af321b29aeaed9eed0502511.
Target not yet established. All 403 inherited rows re-derived, four added;
original ledger and earlier recounts preserved. No endpoint premise removed,
added or weakened. No new proof/theorem, implementation or release pin change.

Recount 2 → 3: rows 403→407; T/P/C 26/372/5→26/376/5;
OPEN 110→103; REDUCED 154→176; EVIDENCED 12→14;
CLOSED-ON-RESEARCH 87→87; CLOSED-ON-CANDIDATE 40→27.
On the same inherited denominator, OPEN is 99. Source-only closures are 26;
V270's scoped axiom-route diagnostic adds the 27th. Eighteen unsupported
source-closure labels become REDUCED under the stricter rule. Op51 stays OPEN.
OPEN buckets a/b/c: 51/50/9→44/51/8. Candidate closure import credit:
research 0, candidate 17, neither 10. Import paths are not deployed discharge.

Corrections: D226 duplicates op229; D235 maps five operation numbers to wrong
row IDs; D219's full V269 closure is unsupported (only axiom slice); D223's
30-entry inventory and no-callback-hypothesis-list correction is supported.
Timing D216 is measured EVIDENCED. RunJoin counts stay 2→2/8→8/6→6;
constructed-candidate initial/causal do not reduce deployed P. T remains three
proposed fields awaiting owner adoption. Noncanonical op121 disagreement is
retained, non-row; canonical-domain and two reachability obligations added.
Later cb5 op51 repair and srcid6 cache/protected-source reports are disclosed,
not silently substituted for the requested dispositions.

Measured/checked: 20/20 Lean statement-check slots, 19 green, one missing-object
diagnostic; no Kani. No coherent release replay. Existing branch/source/native
receipts are reused with immutable pins; no new runtime measurements. Original
374 non-LOG defining-source hashes still available unchanged; 25 LOG-defined
rows re-read. Every status/dependency is in ../ROWS3.md and rows3.json.

| Attempt / module | Exit | Wall | Peak RSS KiB | Swap | Source revision |
|---|---:|---|---:|---:|---|
| 38600 / PV_Ledger_Recount3_Callbacks1 | 0 | 0:01.52 | 4274804 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38601 / PV_Ledger_Recount3_Callbacks2 | 0 | 0:01.49 | 4276960 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38602 / PV_Ledger_Recount3_Callbacks3 | 0 | 0:01.47 | 4277292 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38603 / PV_Ledger_Recount3_Callbacks4 | 0 | 0:01.49 | 4277784 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38604 / PV_Ledger_Recount3_Callbacks5 | 0 | 0:01.49 | 4275000 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38605 / PV_Ledger_Recount3_Callbacks6 | 0 | 0:01.47 | 4280984 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38606 / PV_Ledger_Recount3_Cb3 | 0 | 0:01.46 | 4276632 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38607 / PV_Ledger_Recount3_Dictionary | 0 | 0:01.56 | 4286528 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38608 / PV_Ledger_Recount3_Formatter | 1 | 0:00.08 | 190756 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38609 / PV_Ledger_Recount3_RwCompression | 0 | 0:01.47 | 4288984 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38610 / PV_Ledger_Recount3_RwModel | 0 | 0:01.48 | 4288856 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38611 / PV_Ledger_Recount3_RwSource | 0 | 0:01.62 | 4284776 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38612 / PV_Ledger_Recount3_SourceIdentification | 0 | 0:01.40 | 4093100 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38613 / PV_Ledger_Recount3_SourceConsumer | 0 | 0:01.41 | 4085288 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38614 / PV_Ledger_Recount3_RunJoinEndpoint | 0 | 0:02.76 | 4278016 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38615 / PV_Ledger_Recount3_RunJoinTrust | 0 | 0:02.56 | 4280732 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38616 / PV_Ledger_Recount3_RunJoinCandidate | 0 | 0:02.47 | 4295336 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38617 / PV_Ledger_Recount3_JoinConsumer | 0 | 0:01.58 | 4279568 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38618 / PV_Ledger_Recount3_JoinCanonical | 0 | 0:01.65 | 4294856 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |
| 38619 / PV_Ledger_Recount3_Headline | 0 | 0:01.91 | 4209004 | 0 | c11ca981ce6d082333ac9ba95938daf3e9118dcf |

Accepted #print axioms reports use only propext, Classical.choice, Quot.sound.
Exact commands, source hashes, direct import source/object hashes, full errors
and axioms: receipts.json, *-inputs.txt, out-*.log, time-*.log. Current launcher
TasksMax=64; all scopes MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0, Lean -M7000,
one at a time. Preflights all allowed; no retries, cap or infrastructure edits.
38608 failed on missing PDict_OwnedCorrect262.olean; its distinct coefficient
helper is not certified. The original D219 audit supports the scoped axiom
claim. Failed/sorryAx outputs on other branches are never accepted here.

Stopped because all rows are re-derived and all 20 statement-check slots used.
Next concrete deliverable: V240/op223 full shipped/extracted-source law for
arbitrary slices and complete Result, removing V164's last P_source_p6.
V163 actual model/bytes, deployed RunJoin, E1/E2, L1/L2/L3, client/adoption and
release dependency/axiom closure remain. No sibling/root edit, merge, push,
or wallet/key/fund operation. Only task-generated helper objects are removed
from the host; original source/evidence/caches are retained.
