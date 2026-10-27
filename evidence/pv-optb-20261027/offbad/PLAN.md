# D262 continuation

Base b654d6d8b176144a87a25d3dd5140f1f961a1691; branch codex/pv-optb-20261027.
100 new Lean attempts; 4 Kani control-only ceiling. IDs 44600–44899,
44897–44899 reserved for final three audits. Historical receipts remain intact.

All host scopes use the existing run2.py and env/J.json read-only, private
lean-private and lean-objects directories under the assigned host directory.
The shared run-joint.sh hardcodes shared source and object writes; therefore
it cannot satisfy this turn's explicit prohibition on writing shared env-J
sources. No launcher or environment is edited. The same reservation script,
6G/8G/swap0/Tasks64 caps, Lean -M7000 and 900-second limit are used.
The private object overlay initially lacked the R1Z import. Attempt 44600
failed before elaboration; 44601 changes the dependency environment by adding
read-only symlinks to the existing env-J closure. No shared object is written.

Proof sequence: fiberwise off-bad factorization; existing-event projections;
public predicate / firstGood synchronization; actual retry control; precise
source-body obligations; joint experiment transport; endpoint; audit.
No concrete finite function-space normalization. No full replay until focused
proofs and dependent bridge succeed. No shipped-code changes.
