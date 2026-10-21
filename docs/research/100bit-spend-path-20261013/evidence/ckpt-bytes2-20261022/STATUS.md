# Checkpoint bytes continuation

Branch codex/cx-ckpt-bytes2-20261022. Additive Lean modules and tools only.
No shipped code, existing Lean, session A candidates or other worktree changed.
No env J attempts used. Local Lean uses the private object directory, shared
mkdir lock, -j1 -M4400 -DElab.async=false and inherited pinned dependencies.

## Stage 1 — aggregate body byte meaning closed

`CheckpointBytesBody.fields` concretely maps extracted Prepared/Accumulator
fields into the raw Fields carrier, including physical queries, coordinates
and every weight. `body_byte_c5` proves success and exact C5 body byte meaning
for every Usize index below 1736. Premises: every raw field is canonical,
all 22 queries are below 262144, weights length=64 and saved next=10.
No section-success, per-block equality, whole-body equality or checksum
premise is supplied. No distinct-query premise is needed for byte writing.
`body_block` uses CheckpointBytesLookup and the 18-entry width table.
The indexed vectors remain symbolic; no 1736-byte buffer or 64-field writes
are normalized. The generator emits named section theorem applications.

Final attempt CheckpointBytesBody-4: exit 0, wall 16.721661082934588 s,
peak RSS 3720691712 bytes, swaps 0. Both #print axioms reports:
[propext, Classical.choice, Quot.sound]. Full source revision, exact command,
source/import/object hashes and dependency fingerprint are in receipt.json
and manifest.json. Attempts 1–3 preserve namespace/elaboration and rewrite
failures; compiler recovery axiom reports are rejected as release evidence.
Attempt 3's theorem proofs were standard but the file had a redundant tactic
error; only attempt 4 is accepted. No limits raised or unchanged rerun.

Generator preflight: `python3 -B tools/ckpt-bytes2-20261022/generate_body.py --check`.
The next byte consumer is whole-list materialization/checksum congruence,
then exact-width production section decoding and its concrete ResumeOps
implementation at OraclePortCkptAbi5Stage.reached_stage through strictStage.
The inherited raw-fields reference encode_c5 checksum composition is reused;
this stage does not assert production writer/reader/allocator adoption.
