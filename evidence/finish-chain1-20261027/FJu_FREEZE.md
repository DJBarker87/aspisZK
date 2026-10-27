# Source, tool and artifact assessment

Starting revision b54cbda4b1c85d7c3223988a3ad1711c8b734d5d in this assigned
worktree. Actual branch codex/cx-finish-chain1-20261027. Stage source revisions
and exact dirty-source hashes are in every compiler receipt. New Lean modules
only, all FJu_; all other tracked changes confined to this evidence directory.
No existing proved module, shipped source, cfg(kani) harness, ABI, wire format,
parameters, toolchain, ELF, wallet/key, other worker/session-A source changed.

Coherent host workspace reused:
/home/dombarker/project-offloads/codex-cx-sound-int2-20261025.
Existing S2W_lean_host.py and reservation.py launchers remain unchanged.
Lean v4.32.0 executable SHA256
 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550.
Every focused module uses lake env lean -j1 -M7000 -DElab.async=false,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. No package replay or fresh
frozen-release rebuild is claimed; pinned canonical objects are reused and
fingerprinted in receipts. No dependency rebuild was necessary.

No Rust, Kani, SBF build or three-ELF reproduction trigger. Inherited pins,
not freshly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No Rust target, solver temp, second corpus or compiled-object scratch workspace
was created. Delivered prefix objects remain in the shared coherent canonical
workspace for lead reuse, not in git. Receipt snapshots contain sources,
logs and hashes only. Nothing pushed or merged.
