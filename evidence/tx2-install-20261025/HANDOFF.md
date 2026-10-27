# Authenticated TX2 source installation on the accepted pair

Branch `codex/cx-tx2-install-20261025`, base
`87a79f0184316e40b99d19999669122b63362ae4`. Local commits only; no push.

The requested **same-execution TX2 installation row is checked under the
retained FinT hypotheses**. S2 and the 100-bit release target remain open.
This is not unconditional query arithmetic, a complete source-to-model
refinement, an oracle-history join, or a deployed soundness theorem.

## Exact result

`AspisR1.Tx2I_Accepted.accepted_pair_claims_tx2`,
`lean/Tx2I_Accepted.lean`, builds directly on
`AspisR1.Op3I_Accepted.accepted_pair_claims_op3`. It destructures that theorem
ONCE and passes THAT `cuts.second`, with the same `s.pub`, `s.proof`,
`s.checkpoint`, actual SDK digest, unit hash and observer None, to the
concrete authenticated TX2 body. It retains all predecessor witnesses and
conclusions, including TX1 header/Claims/Required14 continuation, account
observations, ordering, accepted wrappers and unchanged second heap.

`Tx2I_Install.install` replaces only adapter op11 with the existing extracted
`VTop_Stages.verifier.candidate.tx2_authenticated`. Its stage replaces only
op3 and op19. Exact record-restoration theorems prove every other adapter
and stage slot is retained; TX1 op10 remains the predecessor installation.
No `VTop_Entry.install` substitution replaces TX1.

For TX2 shape, `Tx2I_Install.shape` calls the SAME
`Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops`, transporting nominal
Variant/Error constructors. The composed theorem derives the source call's
S2 return, `Op3I_Install.sourceBody s.proof = ok (.Ok .S2)`, and
`OraclePortHeader.accepts (bytesOf s.proof.val) = true` on these TX2 bytes.
No header or whole-parser success is a new premise.

For finish, op19 is exactly `Port4D_FinishInstall.finish finishOps`, whose
parent is `Port3_NativeFinishBody.verifier.finish_relation
(Port4D_Round.native finishOps)`. `Tx2I_Cuts` inverts the original extracted
control flow, with a definitionally equal split at the query return. It
returns the actual resume Prepared/Accumulator, op6 query return, pending
weights, op9 flushed slice, Vec mutable-back function and finish View.
The exact state is
`a = {returned with weights := back flushed}`. Both the deref_mut equation
and op9 call are exported; no independently chosen complete state replaces it.
The actual finish call succeeds on that state.

`Tx2I_Finish.accepted_finish` applies **FinT_Model.finish_value itself** at
that `v,p,a` and the actual resumed `saved`. It exports the full FinT Boolean
source/frozen2 equality and installed-finish/typed-check equality. The
`FinT_Returned.returned_state` / `OraclePortFrozen2.finish_value` reduction
is inherited inside that proof. Together with the derived finish success,
the equalities imply the frozen verdict is true. This is success-conditioned
value transport; Result/error/effect and oracle-log transport remain separate.

## Before/after and premise audit

Complete statements are `before-statement.lean.txt` and
`after-statement.lean.txt`. `premise-audit.json` records a literal comparison:
remove only the added TX2 conclusion, reverse only the dictionary
specialization and remove the new stage/finish dictionary parameters; the
remaining statement is BYTE-IDENTICAL to the predecessor. No original
outer Prop premise, quantifier, carrier, failure event or conclusion changes.
This restricts an arbitrary-operation family to its source instance; it does
not prove equivalence with every old dictionary.

D188 AeneasExtraction is retained at precisely this installed SDK dictionary.
There is no extra extraction association, whole-body success premise,
whole-verifier equality, cryptographic trust item, or hidden conclusion in
an input structure. SDK/runtime/std/allocator/native-wrapper/syscall/oracle,
expanded-child/marks, writer/reader, checkpoint-history, P2Prime and other
child obligations remain specialized exactly as before.

All new owner laws occur explicitly in the post-existential conditional
finish conclusion. Their binder block in Tx2I_Finish is BYTE-IDENTICAL to
FinT_Model's block: RoundValues and alpha/weights/pair/dot returns, input/query
bindings, matching read/decode, pairing_S3_S5_S9, matches_S4_S7,
semantic_S3_S9, dot_S5, canonical_S3_S4_S5_S9, saved_ten and twelve. None is
discharged or changed into cryptographic trust. In particular the actual
op6/flush-to-twelve and resume-to-saved-ten semantic laws remain named
conditional implementation obligations; this task discharges the previously
missing TX2 installation and SAME-argument connection to FinT, not those laws.

Non-vacuity: `Tx2I_Nonvacuity.extraction_satisfiable` constructs the specialized
D188 association for arbitrary remaining dictionaries, using its existing
owned stages and digest. `shape_success` checks the symbolic57607-byte
Op3I fixture; `finish_success` gives an actual source-finish success without
a finish-success premise. `Tx2I_Witness.authenticated_success` checks an
entire authenticated TX2 success with shape and finish still installed and
concrete pure std/remaining leaf fixture operations. This is consistency
of the residual operation interface, NOT production arithmetic certification,
proof validity, or joint inhabitation of all unchanged native/runtime/
cryptographic and FinT owner hypotheses. The fixture is outside the top
closure's import dependencies and supplies it no premise.

## Validation, resources and frozen target

12/80 Lean attempts (zero dependency builds), 0/40 Kani. Failed elaborations
002,005,007,009 and their exact sources/logs are retained; their sorryAx
diagnostics receive no proof credit. 010 includes a temporary trace_state;
011 removes it for the final source. No unchanged source+dependency retry,
timeout, memory kill, cap increase or package/frozen-manifest replay occurred.

| Target | Attempt | Exit | Wall s | Peak RSS KiB | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
|Tx2I_Finish.lean|004|0|2.335904|5169252|0|a651e3de3d + dirty source|
|Tx2I_Accepted.lean|006|0|2.455956|5174224|0|9af90ae9de + dirty source|
|Tx2I_Witness.lean|011|0|5.051933|5955076|0|8e850742fe + dirty source|
|Tx2I_Audit.lean|012|0|1.928443|5138840|0|a40fd04b70 + dirty source|

Every new theorem's final #print axioms is exactly
`[propext, Classical.choice, Quot.sound]`. 012 audits them all together and
prints the existing D188 fields. Receipts record exact command, target,
revision/dirty state, source hash, selected direct dependency/sidecar hashes,
Lean binary hash, exit, wall, peak RSS, swaps and cgroup limits.
`validation-summary.json` checks every source snapshot and final passing
source hash, cap, swap, axiom and no-duplicate-retry condition.

All attempts used the coherent
`/home/dombarker/project-offloads/codex-cx-sound-int2-20261025` cache and its
UNCHANGED S2W launchers, one module at a time with
`lake env lean -j1 -M7000 -DElab.async=false` in individual scopes:
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. No shared existing
source/object or launcher was replaced. Final audit reservation inspection
showed one other worker scope (op4p-kani005); this task reserved8GiB.
All this task's jobs are terminal; other workers' jobs were left alone.

`final-object-metadata.json` records hashes/sizes without binaries.
`source-boundaries.json` pins reused source/extraction/manifests and verifies
all three current VTop source-span hashes against the original extraction
receipt. No extraction was rerun. Reused SInt2 objects are the accepted pinned
selection documented in its handoff, not a new coherent release rebuild.

Only new Tx2I_ modules and this evidence directory changed. No shipped file,
cfg(kani) module, session A candidate/live worktree, key, protocol parameter,
wire format, feature or security metric changed. No Rust/Kani/SBF rebuild
trigger fired. Inherited ELF pins, NOT newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Next concrete deliverables: instantiate resume saved-ten and query/flush
`twelve` laws on these exported actual arguments; retain the named session A
arithmetic laws until supplied. Other TX1 scan/batch, canonical source/model
order, rejected query prefixes, runtime/source-to-ELF and headline obligations
remain outside this row. The release target is not yet established.
