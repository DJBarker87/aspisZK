# Native loop association register

Current status OPEN, pending the membership value domains. Native and model
facts are distinct; no complete Rust result is inferred from source identity.

The SAME state is QueryScan(accepted22, accepted_len, draws); its invariant is
length<=22, draws<=64, canonical18-bit cells, inactive-zero cells. The physical
word iterator's next runs before testing length/draw fullness. The supplied
word is the masked little-endian word of the SAME block at the SAME cursor.

Reused native facts (source/receipt hashes are in NHK_REUSE.json):
- NHB_K030/031, arbitrary32-byte block and cursor0..8, including exhaustion.
- NHB_K053/054, arbitrary bounded scan pre-state, current candidate/remaining
  cursor, one local membership call, exact prefix window, post-increment draw
  count, full22-cell result by arbitrary output window, arbitrary Bool reply.
- NHB_K043/044, stopped-state identity; NHB_K050/051, block-end false with no
  extra stop test even when the last word filled the survivor list.
- NGQ_K046/047, arbitrary scan child reply at a block boundary, exact selected
  block/prestate log and carried-state window; NGQ_K058/059, native range next.

The membership Bool cannot be replaced by the coherent predicate until its
precise length's certificate and domain are available. The stopped path calls
no membership helper. Each continuing call has length<22/draws<64, not the
stronger length<=10 domain. NHB_Canonical.decoded/frame_preserves and
NHB_Inactive.frame_preserves provide the domain without assuming membership
correctness or sampler success. Missing lengths stay explicitly open.

NHB_WordTrace.source, NHB_BlockTrace.block_source/walk_source and
NHB_OuterState.association provide rule-B word/block induction, first stop and
carried advance7 selection. NHB_Sampler.decode_source/cohort_source preserves
the full Result on the exact blocks and advances. No model trace is chosen
independently of a physical invocation. Transcription provenance is recorded
in NHK_TRANSCRIPTION.md; the absent original v7 emission is not fabricated.

Next deliverable: complete membership partition or a precise failed native
window edge, then consume those SAME native cuts in the trace producer. No
XRn join, success-only child, hidden whole-output equality, new trust row or
schedule change is introduced.
