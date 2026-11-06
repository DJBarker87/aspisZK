# NKY row bridges handoff

Target not yet established. Work in progress on TX1:235 and TX2:216/218 only.
Baseline NKW ledger20: 560 CLOSED / 0 QUALIFIED / 39 OPEN of 599.
No closure or ledger delta is claimed before focused proofs and combined audit.

Branch codex/cx-row-bridges-20261107. Own host workspace
/home/dombarker/project-offloads/codex-cx-row-bridges-20261109;
CARGO_TARGET_DIR is its NKY_target; TMPDIR is its NKY_tmp.
Budget 30 Kani / 80 Lean / 0 extraction. Serial capped scopes, admission
exit 0 AND allowed:true; MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64,
Lean -M7000. No cap/timeout increase or unchanged timed-out rerun.

Seed order: retained NKW export, NKI export, NKP final export, then coherent
NKW fallback objects. Copies only into own workspace; all imported object hashes
will be recorded. No shipped-source, sibling/session-A worktree, cache or
infrastructure mutation. No key/account operations. No push.
