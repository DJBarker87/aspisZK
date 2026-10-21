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

## Stage 2 — exact-width production K section

Production Reader source is copied verbatim into the independent tools crate;
source_check.py verifies its identity, raw::<16>(), N-byte cursor advance,
whole checkpoint length and final-cursor guards. No shipped source changed.
Kani k-section-current-1 checks the actual production field decoder, no stubs,
on arbitrary 17-byte backing data: the cursor ends at 16, success iff all four
LE limbs are below P, the output has exactly those limbs, and its encoding is
the first 16 bytes. The arbitrary seventeenth byte is a later section byte.
This proves no noncanonical width is supplied by Reader.k; the standalone
K::from_le_bytes / decode_k_spec still accepts a trailing byte on direct calls.

CheckpointBytesReaderWidth.exact_k_section proves exact slice, 16-byte width,
cursor advance and unchanged backing at every bounded cursor, for arbitrary
decoder result and panic continuation. exact_k_width excludes a seventeenth
byte from the typed array. The theorem explicitly leaves decoder adoption
separate, rather than claiming a generic callback is the concrete Rust instance.
Final Lean attempt 3 is standard axioms only; full metrics and revision in
manifest.json. Attempts 1–2 preserve literal/platform-width elaboration failures.

Final production Kani target: ['timeout', '300', 'cargo', 'kani', '--manifest-path', 'tools/ckpt-bytes2-20261022/Cargo.toml', '--lib', '--exact', '--harness', 'proofs::k_exact_section', '--no-assertion-reach-checks', '--solver', 'kissat', '--output-format', 'old', '-Z', 'unstable-options', '--cbmc-args', '--object-bits', '10', '--unwinding-assertions'].
Exit 0, wall 1.287706813076511 s, peak RSS 62132 KiB,
swaps 0; #print axioms N/A (Kani). Source/dependency pins, revision,
exact cgroup and MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0/TasksMax=64
are in kani/k-section-current-1/receipt.json. Reservation preflight retained.
The first Kani launch failed at compilation because the isolated host copy
lacked tools/r1-builder-reference/tree.rs; no proof ran. The second passed
against an inherited sim.rs differing from this worktree. That unused file
was synced into this task's host directory and the final gate rerun against
current source; the earlier result is superseded, with evidence retained.
No other workspace was edited. No frozen ELF rebuild trigger is present.
