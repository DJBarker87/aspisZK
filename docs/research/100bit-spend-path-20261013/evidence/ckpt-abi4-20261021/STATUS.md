# Checkpoint ABI pass 4

Base `9f42fc11c`, branch `codex/cx-ckpt-abi4-20261021`. New Lean modules
only; shipped sources and sibling/session-A modules are read-only. No push.
The complete checkpoint cone and AcceptedRunJoin remain open.

## Stage 1: frozen caller audit and interleaving obstruction

`callers.json` pins exact TX1/TX2, entry/Pool, writer/resume and heap excerpts,
plus S10 pass-3 evidence. Regenerate/check with `callers.py`. These are source
observations, not semantic source joins. The frozen stage-1 entry reaches
`first_decoded → verifier::tx1 → checkpoint(&p,&a,proof,public_bytes,hash)`
after batch 0, query_loop(end=10), and pending.finish. The Pool stage-2 entry
borrows accounts[6], reconstructs public bytes and passes the proof suffix and
checkpoint to tx2_authenticated → tx2_common → resume, before batch 1.
All three writer digests and all three successful reader digests are retained.
Other Pool/semantic hashes must also be accounted for by the complete driver.

**Target obstruction:** the checked current definition of dV_frozen contains
no checkpoint stage. It short circuits six slot programs and then checks
arithmetic. The packet instruction's “checkpoint stage” is not present in
this source revision. The user approved the port, not an unannounced change
to its definition/probability consumer. This item stops at the precise missing
source/model transport; it is not a proved counterexample to every possible
complete Rust/model verifier identity.

`OraclePortCkptAbi4Interleaved.interleaved_not_erased` extends the earlier
obstruction to an arbitrary prefix before the checkpoint. Authentic saved-ten
write/resume adds six reads between otherwise unchanged batches, so equality
of accepted verdicts and CFG dominance cannot justify that substitution.
This theorem is parameterized reference semantics, not Rust provenance.
Attempt 1: exit 0; wall 13.298869375 s; peak RSS 3,579,658,240 bytes; swaps 0;
source revision `9f42fc11cc715bd0475d8981ac98851b49dce9ae`. Both axiom reports
are `[propext, Classical.choice, Quot.sound]`. Exact target, command, source
and dependency hashes, logs and metrics are in manifest.json and the attempt
directory. No coherent full replay is claimed or justified yet.
