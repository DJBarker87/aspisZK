Successful record payload composition, Lean4.31

ExtractedRecordPayloadSoundness.parse_record_full_payload has only row>=14
and actual generated parse_record row record = ok(Ok payload) as premises.
It proves that List.toChunksExact32(payload.val) has empty remainder, its chunks
flatten to exactly payload.val, and every such chunk is CanonicalChunk.
Framing derives actual validator success; the partition derives divisibility
from the successful row table, not an assumed length. No alternate payload,
default byte or added canonicality premise is introduced.

CanonicalChunk fixes an Array U8 32 with exactly the raw chunk bytes, each of
eight actual LE4 words below2147483647, and the exact nested packed result's
c1=QM31.ZERO. This high-component constraint is QM31-subfield membership,
not M31 descent. Rows below14, including the commitment root record, are not
asserted canonical field payloads. Invalid rows cannot satisfy parser success.

The first focused check passed,16.721s, sampled process-group RSS2801440KiB,
process maximum RSS2215608320 bytes,process swaps0. System swap is recorded
separately and was preexisting. The theorem uses only propext,Classical.choice,
Quot.sound. Receipts pin exact sources, retained prerequisite objects, compiler
runtime dylibs and checkout. The runner uses lake env lean,-M3500,sampled4GiB
process-group stop and180s timeout; it is not a cgroup. No cold dependency build
or unchanged source replay ran. Prior failed component attempts are retained
in their own bundles. WorkerB independently reviewed the exact signatures and
source hashes, without a second compile.

OPEN: Rust-to-extraction correspondence, Prefix::parse/whole-stream provenance,
all33 protocol-row and transcript-state mapping, late records, concrete semantic
field translation, first-read/hash effects, runtime preservation and one-kernel
4.32 integration. This closes one successful extracted record payload only.
