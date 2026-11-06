# NKX legacy Pool removal

Status: in progress; no release claim. Branch codex/cx-legacy-removal-20261107.
Authorized source scope: programs/aspis-pool only. Frozen reference:
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Remove ASIN/ASDI/ASPT/ASWD/ASPP/ASPF/ASPX;
retain all seven pair-forest/pair-afterstate roots, including disabled routes.

Stages: inventory and source surgery; byte identity and tests; reproducible ELFs;
final receipts. Commit after each stage, no push or deployment.
Budget: at most 12 build/test scopes, 0 Kani/Lean/extraction. One admitted scope
at a time, MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64.
Host workspace: /home/dombarker/project-offloads/codex-cx-legacy-removal-20261109.
Every scope requires >=40 GB free and reservation allowed=true with exit 0.

Security impact: remove legacy externally callable surface; no security theorem,
cryptographic assumption or 100-bit conclusion established. Retained function
text and verifier artifact pins must be checked; Pool artifact pin is superseded
only after measured reproducibility. No keys, wallets or funds are accessed.
#print axioms: N/A (engineering job).

Source stage: seven dispatch routes removed; 291 frozen functions removed, including 54 tests; one new rejection test. Surviving function text differs only at process_instruction. Refined inventory closure: 422 exact body/full-function matches; six spurious conservative edge targets (seven induced rows) documented, no actual pair-forest change. Protected crates/, r1-cost-probe/ and Cargo.lock diff is empty. Tests/ELFs pending.

Validation stage: shared AS8I codecs restored verbatim after the first compile
identified their missing import. Final gate: 427 direct frozen/inventory body
and full-function checks pass, all retained pair*.rs files byte-identical,
only process_instruction differs among surviving functions. Deleted functions:
289, including 54 tests. Final optimized tests: deployed 67/67, default 36/36,
disabled routes 67/67, audit-feature union 72/72; all 72 remaining source tests
are matched to executed names. Frozen deployed baseline: 118 unit + 2 ABI.
Two failed compile scopes are retained: initial thread spawning (fixed own
runner affinity, same caps) and missing shared codecs (restored frozen source).
Scope use so far: 7/12, no timeout/OOM. ELF stage pending.

Admission timing deviations: one baseline retry occurred after about 65 s
instead of 180 s (it did not launch); one tests-deployed retry occurred after
about 136 s and launched only after allowed=true, exit 0 and the inside-scope
barrier passed. These are procedural deviations from the prescribed retry
interval; neither bypassed a refusal. The tests-all refusal was retried after
more than 180 s. Complete original admission logs are retained.
