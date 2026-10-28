# NBP U02 atomic digest and payment codecs — CLOSED local

Status: all16 local members CLOSED on the domains below. No headline premise
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

No U02 member remains open. U01 remains reused CLOSED.

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

## Parent payment codecs — CLOSED local

| Member | Full selected-model Result | Native association | Domain |
|---|---|---|---|
| decode_pool_v1_private_transfer_public_v1 | NBP_TransferDecode.result/fixed (L066) | K033 | Every Slice length: wrong lengths reject before reads; exact216 arbitrary bytes use complete native Result/record equality. |
| decode_pool_v1_withdrawal_public_v1 | NBP_WithdrawalDecode.result/fixed (L061) | K034 | Every Slice length; exact216 arbitrary bytes as above. |
| encode_pool_v1_private_transfer_public_v1 | NBP_TransferEncode.result (L070) | K031 | All raw public records; exact validator error or full216 output. |
| encode_pool_v1_withdrawal_public_v1 | NBP_WithdrawalEncode.result (L071) | K032 | All raw public records; exact validator error or full216 output. |

NBP_PaymentModel defines the pure full Results and byte arrays explicitly.
Decoders retain source order: length, header, transfer's fee/reserved check,
common fields, recipient/change digest Results, then final validator.
Withdrawal reads exact amount148..152 and destination152..184. The full
Result laws include every rejection, not only accepted-class values. No
successful callee or desired output is supplied. Their ALL-length proof
inverts the actual fixed-width conversion: its failure returns WrongLength
before any index; on equality its SAME bytes become the216-byte carrier.
Native K033/K034 exhaust the exact216-byte class. For every other native
length, the frozen initial try_into length test rejects parametrically
before inspecting content; there is no claim that bounded Kani slices
exhaust arbitrary lengths.

Encoders compose the CLOSED validators/projections, initialize216 zeros,
use CLOSED encode_common on that SAME pre-state, and write exact suffixes.
Transfer preserves zero fee148..152 and writes recipient152..184/change184..216;
withdrawal writes amount148..152/destination152..184/change184..216. Native
K031/K032 retain the real validators and code bodies with only the CLOSED
digest serializer substituted as registered. The exact byte/frame laws in
NBP_ArrayIndex and K019–K029 derive every copy domain; no canonicality is
required by the serializer, and canonicality is not smuggled in as a caller
precondition.

The only source loop (digest encoding) uses ONE native arbitrary-prestate
iteration and the reused Lean induction. No parent216-byte loop exists or
is unwound; std memory-copy bounds256 cover the largest216-byte carrier.
All Kani runs validate the frozen dependency graph before execution, run
offline/optimized, and leave Cargo.lock unchanged. The new copy shapes have
adequate bounds; inherited K019/K020 credit remains subject to KDX exposure
review. Compiler/platform/P6/ABI and source-to-ELF association are retained,
not promoted to a deployed claim. Coherent slots stay43/44.

This closes local U02 source/cohort helpers only. Actual caller dictionary
installation and the composed S2/deployed soundness theorem are not claimed.
No XRn_Join or stand-in, new axiom, security assumption, trust item or headline
premise removal. Existing prepared_claim bridge LPt is reused; this lane
claims no new closure of prepared_claim. U00's two exact open members remain
in NBP_U00_BRIDGE.md.

Initial co-import/axioms audit NBP_L073 passes:52 selected roots (including
EVERY new top theorem), only propext/Classical.choice/Quot.sound or none.
Command lake env lean -j1 -M7000 -DElab.async=false -R NBP_generated
-o /home/dombarker/project-offloads/codex-cx-tx2low-cache-20261028/NBP_Audit.olean
NBP_generated/NBP_Audit.lean. Exit0, wall2.0109406640403904s,
peakRSS5116504KiB, swap0. Exact source revision,source/direct-object hashes,
caps and all printed lines are in NBP_L073/receipt.json. This is a focused
coherent new-module audit, not a new full frozen release replay.

The FINAL byte-matched co-import/axioms audit is NBP_L075: exit0,
wall1.8260754630318843s, peakRSS5119900KiB,swap0; same52 selected roots and
standard axioms only. L074 recompiles the exact final DigestDecode source
whose only difference from L015 was removal of trailing whitespace. L075
refreshes its dependent audit for that source/artifact correspondence; it is
not an unchanged regression rerun. NBP_FINAL_SOURCES.json matches EVERY final
module byte hash to its latest passing source snapshot.
