# NBP U02 atomic digest and payment codecs

Status: twelve of sixteen local members CLOSED; four OPEN. No headline premise
removed. RPx_Deployed.deployed, L154 statement parameter, narrowed D188,
frozen3, RuntimePersistence and approved game fields unchanged. S2 and the
100-bit deployed target remain unestablished.

## Digest decoder — CLOSED local

`NBP_DigestDecode.result` (NBP_L015) proves the exact selected
`AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical` Result on
EVERY32-byte array. `decoded` tests words in source order, returning the exact
NonCanonicalDigest error or the complete eight little-endian words. There is
no supplied success, canonicality or desired-output hypothesis. The replacement
for NBG_L074 splits first rejection into eight independent fixed-prefix facts
(NBP_DecodeWord.reject0, NBP_Decode1..7.result) and all-canonical success
(NBP_DecodeSuccess.result), then composes by exhaustive ordered case analysis.
No heartbeat/depth increase or unchanged failed shape replay.

Native association reuses NBG_K019 unchanged: every32-byte native input, exact
full Result/error, each output coordinate and all-word canonicality. The Rust
function is the same unrolled eight-word decoder, frozen revision
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. `word` is exactly U32::from_le_bytes
of offsets4i..4i+3; `limbs` orders0..7. The native body has no source loop,
allocator, syscall or field multiplication. Existing Kani credit remains subject
to the lead's KDX exposure review. No new Kani pass is claimed here.

Every new theorem has its own printed axiom audit; accepted results use only
propext, Classical.choice, Quot.sound. Rejected diagnostics are retained and
carry no proof credit. NBP_L015: exit0, wall1.7752974109607749s,
peakRSS3869632KiB, swap0; exact target/command/source revision/hashes/direct
objects/cgroup and axiom lines are in NBP_L015/receipt.json. All scopes serial,
admitted exit0 AND allowed:true; high6G/max8G/swap0/tasks64, Lean-M7000.
Coherent SInt2 objects and own persistent cache/Aeneas pins recorded at start.

## Reused and remaining members

Reused CLOSED from NBG_U02_BRIDGE.md without re-proving: unwrap_fixed_slice,
digest_is_canonical, transfer_common, withdrawal_common, require_header,
validate_common, validate_pool_v1_private_transfer_public_v1,
validate_pool_v1_withdrawal_public_v1. Their domains and exact references remain
those in that handoff.

OPEN: decode_pool_v1_private_transfer_public_v1 and encoder;
decode_pool_v1_withdrawal_public_v1 and encoder. Their native checks now pass;
selected full model parent composition remains under validation. U01 remains
reused CLOSED.

Retained caller dictionary installation, runtime/allocator/SDK/ABI/compiler/P6
and source-to-ELF boundaries are not removed. No repository crates/programs
change, no ELF rebuild trigger; release pins inherited, not reproduced:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Digest encoder — CLOSED local

NBP_DigestEncode.result (L017) reuses S2K_DigestBytes.exact on the ACTUAL
selected TerminalDecoder definition, all raw8 limbs. Its loop_exact is a
decreasing-Nat induction, with DigestTotal.body_word/next_row/exhausted proving
the exact iterator association, count<8 byte ranges, one4-byte update and
terminal state. NBP_DigestLayout.bytes (L026) identifies its same output with
the ordered concatenation of all eight little-endian words.

Native iteration association reuses NBG_K020: arbitrary32-byte prestate,
arbitrary index<8, raw value, exact four bytes and all untouched positions.
Standard iter/enumerate supplies indices0..7 in source order; the selected
model next_row/exhausted carries the identical counts/words and derives
arithmetic/copy bounds. Existing Kani credit remains subject to KDX exposure
review. No whole native encoder loop is unwound.

The closed model proofs and native step refer to the same fold: start32 zero
bytes; at indexi setSlice4i of raw wordi.to_le_bytes; stop at8. No output
equality is supplied by a caller. The source loop has no external effects,
allocator or syscall. No new standard-library trust item is introduced.

## Common codecs — CLOSED local

`decode_common`: NBP_K030 (0/588 failed) plus NBP_CommonDecode.result (L034).
Every216-byte input, full error Result and every byte/limb field. The asset
word144..148 rejects FIRST; then the exact80..112 and112..144 digest Results,
then validate_common on pool8..40, deployment40..72, sequence72..80 and those
SAME digest values. Reuses the CLOSED digest decoder and common validator;
fixed-width slice widths/bounds are derived, never supplied as child success.
The native reference checks complete error identity and every record coordinate.
No loop, field multiplication or syscall is involved.

`encode_common`: NBP_K018 (0/191 failed) plus NBP_CommonBytes.result/association
(L057), all216-byte pre-states, arbitrary magic, both kinds and all raw common
records. The exact pure expected value writes magic0..4, version4, kind5,
digest version6, pool8..40, deployment40..72, sequence72..80, digest80..112,
digest112..144, asset144..148. Byte7 and suffix148..216 are preserved.
The seven NBP_CommonTail modules reuse arbitrary-output index/copy/update laws;
they use the actual frozen operation bodies. association reassembles those
bodies by definitional equality; it is not a hypothesized callee result.
The replacement splits the default-heartbeat-exhausted whole normalization,
not an increased limit or unchanged replay.

Every digest encoder invocation admits all raw8 limbs; NBP_STUBS.md pairs the
native substitution with result and byte-layout theorems. Native store checks
K019–K029 check every used source range and frame on arbitrary pre-state.
All new memory-copy gates use unwind256≥216, not the low-bound KDX hold shape.
All accepted new roots print only standard axioms (or none). Exact metrics,
source/object hashes and revision pins remain in the per-attempt receipts.
