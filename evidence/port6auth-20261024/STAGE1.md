# Indexed authentication interface challenge

Source: research 6394df23891e699f4db152110f727b7cac678184; inherited ELF pins
are historical only (default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548).
No new artifact identity gate, shipped source edit or ELF rebuild.

## Before: exact all-world interface

`OraclePortFrozen2Join.AcceptedVerifierJoin source model :=
∀ H i, (eval H (source i)).2=true → eval H (source i)=eval H (model i)`.
`AcceptedRunJoin` adds equality of the full accepted TWO-pass annotated run,
including ordered log, carrier, proof words and verdict. Canonical transport in
`Port1_CanonicalJoin` restricts the source-indexed carrier, but STILL quantifies
over every H, without collision exclusion. Physicality removes ghost-word
choices; it does not establish duplicate payload equality or log equality.

`Port5Q1_Complete.accepted` requires, for all pos<22,
`recovered (index q 2 pos)=some (payload parsed 2 pos)`.
`Port5Q1_Parsed.packed_at` uses this to identify the GLOBAL first-occurrence map
with the actual opening bytes. Therefore this premise concerns all positions,
including parents repeated across batches; it is not just membership or roots.

## Source challenge and retained obstructions

`crates/aspis-r1-cost-probe/src/candidate.rs:92-202` uses u/4 for kind2;
its keys sort `(index<<8)|relativePosition`. Each `batch_tree` starts d=0,
hashes EVERY selected opening, compares only 32-byte DIGESTS of within-batch
duplicates, then calls in-place verification. `batch_merkle_values` allocates
fresh scratch and independently authenticates three roots. There is no byte
comparison and no saved cross-batch duplicate table. Both batches use the same
folded root; this alone is not injectivity. A constant oracle makes the local
leaf digest comparison insensitive to arbitrary payload bytes. This observation
is NOT a counterexample to the full accepted two-transaction spend path.

Retain (do not repurpose as full-source counterexamples):
* `OraclePortAccLogSlot.accepted_slot_logs_differ`: accepted frozen and recursive
  slot logs differ in a constant oracle world.
* `OraclePortAccLogRecoveryWorld.consistent_byte_log_counterexample`: one total
  oracle, consistent permuted byte logs, different indexed recovery results.
* `OraclePortRefineJoinRecoveryObstruction`: recovery/cut permutation failures.
They defeat permutation-only recovery transport, not the current source-ordered
frozen2 identity. No complete accepted-source counterexample to that identity
has been established here. The strong join remains UNPROVED, not declared false.

## After: local recovery and sufficient source experiment

The local replacement takes the SAME two actual native op13 returns, SAME
stored wire, both physical Prepared/model BodyMatches, SAME q, local P6
boundary, actual containing log, first-read bound, existing collision exclusion,
and actual commitment-frame read/selector. It CONSTRUCTS the cut recovered map
and proves every selected payload equality for each kind. No global join enters.
The source producer for batch success is `Port4B_CallerJoin.accepted`; Prepared
roots/queries come from `Port4B_Prepared` and `Port4B_KeyInstall.queries_bound`.
The folded root bytes come from SAME source copy via `Port4B_FoldedCut.model`.
S1 prepare and CK resume/BodyMatches remain local producer obligations; native
op18 is owned by Port6CK. Oracle source-call containment/frame provenance remain
explicit source trace obligations, not borrowed from frozen2 acceptance.

The sufficient probability route must bound collisions ON THE SOURCE experiment
once, transport charged-prefix reads under the same adaptive oracle, and prove
clean terminal checks/no-hit on the SOURCE record. Adding a discrepancy term to
the already collision-charged model failure bound would double charge collisions;
that route is rejected. Source ordered execution equality is not necessary if
source clean checks, exact prefix containment/replay and the original query
budget are established. These are proof obligations, not new trust assumptions.
