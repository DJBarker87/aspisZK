# Authentication premise removal — stage 0

Read the root AGENTS security/proof rules, common/local rules, historical S2
handoff/plan/diagnosis/interface under docs/research/100bit-spend-path-20261013,
C3-BIN route B adoption (2026-10-23 01:20), SInt2/SdkC/SdkD handoffs and
premise ledger. Branch codex/cx-auth-s1-20261026; prefix AuS1_.

Target: extend SdkD_Accepted on the same witnesses, removing the inner
Tx2N_Finish.Outcome authenticated_S1 gate. Current replay theorem is separate
from that joint endpoint. Original folded-root frame reads and original-prefix
recovery still need proof; global experiment/budget belongs to GExp_. No
replacement bundled authentication/source-log premise earns removal credit.

Reuse coherent host workspace codex-cx-sound-int2-20261025 and SdkD_100
LEAN_PATH. All invocations use existing launchers, one module, -j1 -M7000,
MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64. Budget 100 Lean
(including dependencies), 20 Kani; initially 0/0 used. No package replay.
No shipped changes planned; inherited three ELF hashes remain unreproduced.
No key/funds operations. No session A live worktree access.
