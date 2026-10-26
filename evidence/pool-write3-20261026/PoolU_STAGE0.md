# PoolU source composition preflight

Branch codex/cx-pool-write3-20261026, base 83b9c6fbd1. New PoolU_ files only.
Read root security/proof discipline, common/local Lean rules, original S2 ownership,
plan, diagnosis and interface (under docs/research/100bit-spend-path-20261013),
adopted SDK route B, complete lifecycle scope, PoolS/PoolW/PoolV/Hist/Hiq/Hir/SInt2
handoffs and every PoolW/PoolV module. Option B is adopted by the owner.

Actual P1 writes planner ASC8 bytes after optional System CPI. It has no verifier
CPI, and cannot literally write a verifier-returned CP. Keep the inherited native
CP writer/child/copy proof separate. No new runtime item is adopted.

The leaf inventory still lacks actual original planner/caller decomposition,
strict master/lane decoder + PDA + root association on the same source snapshots,
and native/source allocation/cleanup/prefix association. Existing native Kani
receipts are evidence only for the exact classes in PoolW/PoolV handoffs. A Lean
reference composition may not promote these gaps to proved native acceptance.

Host preflight: existing SInt2 launchers and PoolW/PoolV objects present; no other
populated build scope observed. Reuse these objects unchanged. Each prospective
compile uses -j1 -M7000 -DElab.async=false, scope high6G/max8G/swap0/tasks64.
No Rust, Kani, extraction, package or manifest replay is authorized this round.
