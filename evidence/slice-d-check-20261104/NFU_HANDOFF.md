# NFU live handoff

Branch `codex/cx-slice-d-check-20261104`; receipts `evidence/slice-d-check-20261104/`.

Checked result: **2 new composed functions / 2 D rows**; see NFU_CLOSED.json, NFU_CERTIFICATES.json and additive NFU_certify.py. D is 23/343 CLOSED at this checkpoint; driver remains OPEN. The deployed 100-bit per-attempt target is not yet established.

Committed stages: 3879c16c0d8 (scope/error callback), 08c43bb83e5 (record getters). Later work is pending audit/admission; never report it as closure. No push, merge, shipped source, session-A worktree, wallet/key or chain change.

Current receipt counts: {'lean': 53, 'kani': 68, 'auditbatch': 1} out of 100 Kani / 60 Lean / 3 extraction. K014/K020 timed out and are excluded. K015/K021 were NOT launched; no timeout control is queued unchanged. L006/L008/L010/L013 failed and are excluded. Corrected model attempts are L007/L009; retargeted leaf modules L011/L012/L014..L045 pass. Their copied theorem terms are unchanged, imports are private, old global helpers live under NFU_Retarget and unused Phase aliases the canonical NFN owner. Explicit isize discriminant syntax is corrected to the selected canonical adapter. See NFU_RETARGET.json/.diff and NFU_BOUNDARIES.md.

Host workspace `/home/dombarker/project-offloads/codex-cx-slice-d-check-20261104`; retained private cache `/home/dombarker/project-offloads/codex-cx-slice-d-check-cache-20261104`. The cache is never deleted. Seed provenance/hashes are NFU_CACHE_IMPORTS.json.xz/.sha256; all 31 NFQ export hashes pass NFU_NFQ_CACHE_CHECK.json. Use the receipt's pinned LEAN_PATH and selected Aeneas objects. No source substitution from live sibling worktrees.

Each launch uses unchanged S2W_run_host.py, allowed:true AND exit0 admission, one own scope at a time, MemoryHigh6G/Max8G/Swap0/Tasks64; Lean -M7000, optimized offline Rust/Kani with frozen graph validation before every run and unchanged lock afterward. Exact per-attempt targets, exit, wall/RSS/swap/source/dependency/tool pins and axiom lines are in NFU_ATTEMPTS.jsonl and source snapshots. KMX patch is the adopted bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 patch; no private copy stub is written.

Next: finish namespaced compact leaf wrapper, KMX replay of check_one, full iterator/window and validator steps, raw audit, additive admission. Adapter getter/helper results await that same audit. Continue independent remaining members listed in NFU_REMAINING.md; do not stop on Kani exhaustion while Lean obligations remain. Preserve root physical/ABI/source-to-ELF/compiler/library/P6 option-A trust; RuntimePersistence/ReturnData/Memcmp and runtime digest realization remain accepted trust, never discharged here. Inherited ELF pins f8c0ec72..., 63ad3e9c..., 121f3e29... are not newly reproduced: no rebuild trigger has fired.
