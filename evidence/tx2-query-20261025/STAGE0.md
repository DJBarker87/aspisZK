# TX2 query task

Read the root AGENTS.md Security and proof discipline, common/local rules,
S2 ownership/plan/diagnosis/interface (under docs/research/100bit-spend-path-20261013),
C3-BIN 2026-10-23 01:20 route B, and SInt2/Tx2I/Q1/Q2/history handoffs.

Assigned branch codex/cx-tx2-query-20261025; prefix Tx2Q_.
Budget 80 Lean compilations including dependencies, 30 Kani. Used 0/0.
Use the existing coherent sound-int2 host workspace and unchanged S2W launchers;
-j1 -M7000, independent 6G/8G/Swap0/Tasks64 scope per attempt. No package replay.

Target: derive saved_ten and twelve on the actual returned TX2 arguments,
without moving them into a structure or another premise. Retain only the
authorized named owner laws. The base stage dictionary is parameterized;
its op18/op6/op9 need concrete specialization and proved compatibility.
The existing history identifies checkpoint bytes, whereas its retained
writer/reader cone contracts expose header hashes/size only. Q1 additionally
requires actual parsed-wire and indexed opening bindings. These must be
derived, not inferred from byte history or arithmetic canonicality.

No proof/result claimed in this stage; no shipped source or candidate changed.
Inherited artifact pins (not rebuilt): default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
