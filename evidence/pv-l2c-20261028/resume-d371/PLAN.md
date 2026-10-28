# D371 decoder and caller investigation

Entry: 3197fab0ebe160020af494199a25b24940e179a8; worktree
`/Users/dominic/ZK/.worktrees/pv-l2c`; branch `codex/pv-l2c-20261028`.
Read the complete inherited prompt chain and D370 finding. D370 is retained.
No frozen implementation change or domain restriction is adopted by this note.

Remaining authorization: 97 Lean compiles, zero Kani. Consumed D369 IDs are
50300, 50301, 50302. Next 50303; final audit reserve 50397–50399. Native
diagnostics do not consume Lean IDs. One capped host scope at a time.

First enumerate every input to the actual devnet planner compiler calls,
including the pv_client_gate JSON producer, account codecs, generated notes,
hash-derived fields and scalar/byte representations. Inspect the wallet
adapter separately and distinguish it from the selected proof-account client.
Establish decoder range laws before restricting the proposed honest route.
If a raw noncanonical representation is reachable, record its precise route
and owner options and stop under D371. Otherwise prove the decoder/generator
range boundary and continue compiler-to-N3 and N2–N6 association work.

All new native tests must retain source hashes, exact command, exit, wall,
aggregate RSS, swap and revision. All new formal statements need axioms
output and pinned dependency checks. No unchanged release replay is planned.
