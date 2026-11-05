# Native loop association register

Current status COMPLETE under the hybrid (ah) packet. All membership domains and the native word/block association are checked. The initial decomposition below is retained for provenance; the final association section is authoritative. Native and model
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
correctness or sampler success. Every continuing length is now discharged by NHK_MEMBERSHIP_CALLEES.json.

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

## Explicit native contract and final association

NHK_K034 passes proof_for_contract(NHK_word_step) on the mechanically
isolated frozen word body, with arbitrary bounded scan prestate, raw candidate,
arbitrary membership reply and every observation window. NHK_K035 flips only
the returned stop flag and fails the exact ensures, with identical source,
KMX/graph/lock/features and limits. modifies(scan,log) covers exactly the mutable
scan and fresh local observation record; the arbitrary window checks the whole
scan frame. Pre-observation scalars are uniquely available (L021). No old-array
snapshot, writable static or function-pointer property is used.

L021 identifies the Rust NHK_word_ref with L011's G. L011.logged_post aligns
the SAME native after-state, not a fresh model substitute. L013's induction
retains actual cursor/final variables; L014 composes source-order blocks and
full finish Result. The complete membership table discharges the opaque reply
value at every call, with canonical/inactive domains established independently
of correctness for inherited16/18/19. The cursor/native decode/outer cuts are
reused by pinned source/receipt, never replayed.

L016 assembles the chronological Invocation.Cuts into NGQ_Cuts.Trace; L018
exports actual_queries/prefix_transport/exact. L022 combines all41 roots with
RPx; L024–027 pass raw ax2,8 fixtures and the13,483-module zero-defect scan.
No XRn join or new whole-output/accepted-run hypothesis is installed. The
physical-to-source semantic step remains the approved P6/D188 option-A native
contract transport, plus reviewed transcription under(ah); nothing is removed.
