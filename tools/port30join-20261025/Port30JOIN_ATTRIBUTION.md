# Lean replay adapter attribution

Port18COHERENCE_Kernel.lean derives from Lean 4.32.0 `src/lean/Lean/Replay.lean`, copyright 2023 Kim Morrison, author Kim Morrison, Apache 2.0. The original notice is retained in the source; the applicable license is Port18VALIDATE_LICENSE beside it. Exact upstream hashes and complete adapter diff: `evidence/port18validate-20261024/upstream.json` and `upstream-adapter.diff`.

The adapter changes module/prelude/import/public frontend and namespace, uses the default kernel heartbeat limit instead of zero, and rejects unsafe/partial input and project axioms instead of skipping unsafe/partial input. It retains replay traversal, duplicate theorem handling, kernel checking, and constructor/recursor comparisons. No algorithm/program selection changes in this review. Historical receipts and source snapshots remain unchanged.

Port30JOIN adaptation (uncompiled): namespace/imports changed, duplicate-theorem
shortcut removed, strict-v3 ctor/recursor comparison substituted, remaining/pending
completion guard added. Both insertion and replay explicitly throw before any
kernel operation. Selection/group/core-leaf guards are separately reviewable.
Port29 strict-v3 comparator is copied unchanged except namespace/public exposure.
