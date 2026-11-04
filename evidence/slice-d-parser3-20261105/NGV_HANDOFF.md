# NGV parser-chain handoff

Stage 0: initial inspection; no new closure claimed. Assigned branch codex/cx-slice-d-parser3-20261105. Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Only NGV modules and this evidence directory may change. No shipped source changes; inherited ELF pins are not newly rebuilt.

Order: parse_record TX1:151 (full validator and parser substitution), parse_record_at TX1:152 (full borrowed result/error/cursor), expand_semantic TX1:098 (original loop and same-output frame). decode_k is reused CLOSED from NGO; no passing native certificate is rerun. No success premise is permitted. Combined gate uses NGK_COMBINED_IMPORT and RPx_Deployed.deployed, raw ax2 and loaded scan.

Budget ceilings: 30 Kani, 90 Lean/support, 1 extraction. Initially 0 used. One capped scope at a time, admission requires exit 0 and allowed=true; Lean -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. No timeout/cap increase or unchanged killed/timed-out rerun. Retain all trust rows; target not yet established.
