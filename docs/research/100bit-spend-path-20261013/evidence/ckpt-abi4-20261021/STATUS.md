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

## Stage 2: shared/mutable std content and capacity obstruction

`OraclePortCkptAbi4Std.shared_interval` proves the actual imported shared
slice iterator consumes every element of an arbitrary bounded interval in
order, preserving the backing and ending at i+n. `shared_exhausted` proves
its next step at length returns none. `mutable_writeback` proves the actual
mutable next/back operation reads the original element, advances by one, and
writes back exactly via setAtNat at the original cursor. These have no
caller-supplied next/back specifications. They remain std-model results;
adopting read_checkpoint_weights' complete fallible loop and its translation
is still required.

`no_requested_capacity` proves no function on the returned bounded-list Vec
can recover all requested capacities: with_capacity(0) and with_capacity(1)
are the same empty model Vec. This rules out using that content state alone
as evidence of physical capacity. It is **not** an impossibility theorem
for a richer allocator refinement, nor a claim that Rust's actual capacity
always equals the request. Rust try_reserve_exact, Allocation, Box::new,
BumpAllocator availability/high-water and Drop require a richer operational
boundary. No physical allocator availability premise has been disguised as
a std-model consequence.

Final std attempt 3: exit 0; wall 9.420210875 s; peak RSS 2,218,590,208 bytes;
swaps 0; source revision `65b3d0f46`. All four axiom reports use only standard
axioms (full lines in manifest/log). Attempt 1 inspects the live std bodies;
attempt 2's failed list/cursor arithmetic congruence is retained, including
compiler recovery output, and is not accepted proof evidence. A changed
proof resolves it in attempt 3. No memory limit or heartbeat is raised.

## Stage 3: successful strict extracted decoder canonicality

`OraclePortCkptAbi4Decode.decoded_canonical` derives all four raw limb bounds
from `decode_k_spec b = ok (some q)`, with no input-length or external
canonicality hypothesis. `from_limbs_canonical` proves all eight limb bounds
from successful extracted WideExact.from_limbs. `decoded_wide_canonical`
then derives them from successful extracted decode_e_spec itself.
`canonical_words_bytes` lifts the pass-3 single-word projection law to the
complete ordered four-word list, under these explicit bounds.

These are the actual pass-2 extracted **reference strict decoders**, not
an identification of the emitted production reader's call tree with them.
The complete U8/U32 codec bridge to C5.encodeK/encodeE and sparse body_byte
is still missing. In particular, canonical_words_bytes states a mathematical
LE32 projection equality; it is not encode_k/C5 equality. No raw noncanonical
writer input is silently mapped into a canonical exact-field encoding.

Final decoder attempt 5: exit 0; wall 17.072822208 s; peak RSS 3,354,214,400
bytes; swaps 0; source revision `d377690b4`. All four axiom reports are
`[propext, Classical.choice, Quot.sound]`. Attempts 2 and 3 separately checked
the four- and eight-limb parts. Failed attempts 1 and 4 retain the unresolved
branch/let and inferred list-cast goals; corrected elimination, explicit Nat
lambda domain and let reduction resolve those errors. Their compiler recovery
axioms are not accepted. Manifest/source snapshots preserve every attempt.
