# L186 removal packet complete under P7

Branch codex/cx-lowering2-20261026. No push. Only evidence/lowering2-20261026
changed. Shipped source is byte-identical to starting revision9e23364d3563;
actual build revision8953c28138c7e3bc31a9109e84ab3a9864090057 adds only evidence.

All three owner-requested deliverables pass:
1. Private capped optimized SBF rebuilds reproduce defaultf8c0ec72…,
   devnet63ad3e9c… and Pool121f3e29… (full hashes, commands, features, program
   IDs, tool binaries/versions, sizes and resource receipts inSTAGE2.md and
   Low2_build_manifest.json).
2. Machine-checked source pin/compilation manifest covers every named packet
   plus referenced JSON.2,794 exact source references;14 historical S2W
   references use the recorded require_zero-only S4 bridge, mechanically
   verified byte for byte with exact theorem source and standard-axioms receipt.
   No unbridged mismatch. The manifest distinguishes actual compiler inputs,
   Cargo configuration, uncompiled inventory files and verification kits.
3. Existing S10 collectors/checkers replay all140 ordering certificates on
   the rebuilt inputs/ELFs. No changed bodies or coordinate changes; no new
   ordering tooling beyond literal path relocation. SeeSTAGE3.md.

Recheck without compilation:

    python3 -B evidence/lowering2-20261026/Low2_check_manifest.py

Result: evidence_gates_pass_under_retained_P7.
Low2_source_to_elf_manifest.json is the source/certificate/ELF link;
Low2_final_receipt.json pins it and records exact command, exit, wall, RSS,
swaps, source revision, checker/dependency hashes and axioms status.

Before: L186 requires source lowering to frozen ELFs. After: no separate
implementation proof remains for L186 under C3-BIN2026-10-25 13:35: retain P7,
use these reproducible hashes and S10's140 checks. No new premise or trust
item. Existing D188/P6/library/runtime boundaries and all other source/model
ledger rows remain unchanged. The lead must apply the ledger retirement:
editing that shared ledger was outside the explicit worker write scope.
Overall release security target is not established by this artifact gate.

Budget: SBF4/6 (one pre-compilation missing-manifest failure, then three passing
builds), Kani0/0, Lean0/10. No timed-out/memory-killed job; no caps raised.
Initial analysis path/input failures and the local pre-launch NameError are
recorded inSTAGE3.md and retained receipts. No shipped file, key, candidate,
other worktree or shared build cache changed. No binaries committed.
No new top theorem; reused exact S4 #print axioms audit is standard-only.
