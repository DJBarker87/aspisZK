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
