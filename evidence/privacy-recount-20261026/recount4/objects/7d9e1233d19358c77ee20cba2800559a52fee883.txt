# Historical allocation checkpoint — allocation now exhausted

User explicitly requires all 100 Lean / 6 Kani. Do not end while budget remains because of reservation contention. Final 3 charged Lean attempts reserved for TrustAudit10Records/Joins/Trace. No ROW counterexample found. Target not yet established.

The local sequential driver is running in exec session 76008:
`python3 tools/pv-runjoin10-20261027/run-plan.py evidence/pv-runjoin10-20261027/l2-remaining-plan.json 6 60 39039 39038`
It automatically retires each refused ID, waits 180 seconds in 30-second increments, retries with a fresh ID (up to 10 consecutive refusals), and stops on compile failure. Poll via write_stdin, never start another host scope concurrently. Current receipts/used-ID files and tally.py are authoritative. At this checkpoint 56 charged (55 accepted, one corrected early rejection); Kani 6/6 passed; ten refusals. Last successful module F3PrefixBounds ID39064; current refused ID39065; next ID39066 after 2026-10-27 02:13:05 UTC. Do not reuse any ID. Reservation contention has recently admitted about one module per 3-minute retry.

When this driver completes, ordinary charged count must be 97. It ends through plan index65 F6IdentityRow. Then preflight the 3 TrustAudit10 modules (sources are written but uncompiled), commit those new sources path-limited, and run final-audit-plan.json with the next unused ID, exactly the final three attempts. Collector and run-plan enforce this. Do not compile audits early. Fix obvious source-name issues by read-only inspection before their checks.

After final 3: run preflight for all l2-targets into l2-final-cache.json; run object-index.py; tally.py; finish.py; verify report/source/axioms/ID counts, commit evidence path-limited. finish.py writes final REPORT/summary/source audit and asserts 100 charged plus all 3 audits passing. If a final audit fails, report failure accurately; don't misclaim or exceed budget. It may need report-script adjustment for an accurately failed audit.

Do not change host launcher/env/Kani configuration. Actual launcher executable TasksMax is64; header/standing lead text says128. Receipt metadata was corrected to executable64; host caps remain6G/8G/swap0/-M7000. No infra edits. Host target Rust cache was removed after six Kani passes; no more Kani budget. Retain own lean-objects for closure, and hash them with object-index.py. No keys created or destroyed.

Original25 objects all passed IDs39005–39029, pinned research e074829f... and retained in own objects; 25→0. Stage1 PackedPublic/PackedRecords/PackedBinding/CompilerPayload/PackedDynamic passed. These prove conditional source/interface facts only: actual dictionaries, compiler success, selected returned transition and deployed source public binding remain open. Constructed P unchanged {source public binding, trace}; whole deployed rows removed0; runtime/boundary2, fields8, residuals6; T unchanged3; A/B unadopted. Transfer/withdrawal P∧T both OPEN with T hypothetical. Exact statements and source inspection are in P-before-after.json, stage1-obstruction.md, stage2-obstruction.md, actual-fixture-source-pins.json, trace-obligations.md, ledger-accounting.json. Source-root Kani13 retained+6 new=19/21; cells18/19 remain.

New audit sources are untracked until the pre-audit source commit. Existing commits are listed by `git log --oneline ab9f1bfb8f..HEAD`; no push. Keep reporting progress in commentary at least every60s while waiting; each blocking sleep≤60s.

Update 2026-10-27 02:23:50 UTC: ordinary replay progressing in batch again; 75 charged (74 accepted), latest accepted39087 F6NullEntry. The live tally/used files remain authoritative.

Update: ordinary driver session76008 completed. Charged97 (96 accepted); next unused39111. Final audit preflight has exactly three audit sources missing, no missing import. 11 L2 further source objects remain (l2-final-cache.json). Pre-audit source commit is next, followed by final-audit-plan.json.

Final: allocation exhausted at100 Lean (99 accepted,1 rejected) and6/6 Kani. Audits39111–39113 passed. Next unused ID39114, but no compile budget remains. See REPORT.md and summary.json. No driver is running.
