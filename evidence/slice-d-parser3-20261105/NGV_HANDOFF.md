# NGV parser-chain handoff

Stage 0: initial inspection; no new closure claimed. Assigned branch codex/cx-slice-d-parser3-20261105. Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Only NGV modules and this evidence directory may change. No shipped source changes; inherited ELF pins are not newly rebuilt.

Order: parse_record TX1:151 (full validator and parser substitution), parse_record_at TX1:152 (full borrowed result/error/cursor), expand_semantic TX1:098 (original loop and same-output frame). decode_k is reused CLOSED from NGO; no passing native certificate is rerun. No success premise is permitted. Combined gate uses NGK_COMBINED_IMPORT and RPx_Deployed.deployed, raw ax2 and loaded scan.

Budget ceilings: 30 Kani, 90 Lean/support, 1 extraction. Initially 0 used. One capped scope at a time, admission requires exit 0 and allowed=true; Lean -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. No timeout/cap increase or unchanged killed/timed-out rerun. Retain all trust rows; target not yet established.

## Stage 1

parse_record TX1:151 is CLOSED. Full validator scan, parser substitution and downstream NGO decoder caller framing compile coherently with NGK and headline. NGV_A001 passes 19 raw roots, eight fixtures and a 13,497-module clean scan. Additive validator rejects eight corruptions. Exact claim, retained assumptions and evidence are in NGV_BRIDGES.md; all attempts, including failures, remain in NGV_ATTEMPTS.jsonl. No Kani or extraction used. Charge so far: 28 compiler attempts + one optimized audit =29/90 Lean/support. Host seed 125 files /471,063,752 bytes; hashes in NGV_CACHE_IMPORTS.json. No shipped files changed and no ELF rebuild triggered. Target not yet established.

## Stage 2

parse_record_at TX1:152 CLOSED; the additive ledger has two new rows, with the stage-2 raw/scan/source validator gates passed. NGV_AtPacket.result retains original borrowed carrier, full parser/errors and exact next cursor; no successful child premise. Audit A002 has 21 raw roots and 13,499 clean modules. Counts through L036/A002: 35 compiler launches, two optimized audits and one conservatively charged prelaunch input failure =38/90 Lean/support; 0/30 Kani, 0/1 extraction. Expand_semantic remains the sole assigned OPEN member. No trust or shipped source change.
