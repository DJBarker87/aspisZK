# S6 accepted digest inverse and complete payment decoder frames

2026-10-23. S6 remains OPEN; target not yet established. This note extends
S6-ENCODER-TOTALITY-20261023.md. The source scope is the concrete complete
codec reference, with full native types and installed actual std methods.
The historical codec freeze and compatibility with current owned-adapter/H5
stage pins are recorded in s6-current-statement-source-compatibility.json.
No production Rust, source freeze, wire format or security metric changed.

## Enclosing claims established

`AspisS6SourceCodec.DigestRoundtrip.accepted_roundtrip` states:

    ∀ bytes : Array U8 32, ∀ digest : Array U32 8,
      decode_digest_canonical bytes = ok (RustResult.Ok digest) →
      encode_digest_canonical digest = ok bytes

The sole premise is the actual complete decoder return. No independent word
success, canonicality, byte carrier or encoder-correspondence premise remains.
`inverse_spec` exposes the same fact as a total decoder contract, including
noncanonical rejection. This instantiates the complete concrete decoder and
encoder reference, not arbitrary child operations.

The proof uses the checked four-byte field inverse, derives all eight successful
word returns from the actual source control, proves the encoder's exact output
contents, and composes eight symbolic writes. A generic list frame lemma retains
suffix contents; no field arithmetic is unfolded for the write composition.
A 32-element byte expansion uses the warm IntervalCases tactic. No large numeral,
field-value enumeration, native_decide or resource-option override is involved.

`AspisS6SourceCodec.PaymentDecode.common_spec` proves totality of the actual
common decoder and exact accepted byte frames for pool, deployment domain,
anchor sequence, anchor digest, nullifier and asset ID. The digest-frame
witnesses are the actual concrete encoder outputs. Fixed-size conversion
success is derived at each reached range before the source unwrap; it is not
a caller hypothesis. All malformed field and validation errors are retained.

`header_spec` proves totality and the accepted magic/version/kind/encoding/
reserved-byte frame. `AspisS6StdByteSlice.eq_exact` proves the actual primitive
slice comparator equals byte-list equality on all slices, including different
lengths. The comparator's actual use of the byte `ne` operation is preserved.

`transfer_total` and `withdrawal_total` prove both complete payment decoders
total on arbitrary slices, with no fixed-length or successful-child premise.
`transfer_frames` and `withdrawal_frames` strengthen those enclosing contracts:
from each actual successful return they derive an owned 216-byte value equal
to the input, its actual header and common frames, the fee/amount and complete
output/destination frames, and the exact successful concrete validator return.
The validator replay equations are derived from actual calls in the decoder;
they are not assumed at the enclosing boundary. Full native public records,
source Result/error control and all range checks are retained.

This does NOT yet prove either complete payment decoder re-encodes its input.
The remaining serialization frame composition must consume these facts.
The 1880-byte accepted round-trip and SDK/account state/trace port are open.

## Evidence and validation

The source-only packet is selected by
`evidence/s126-current-caller-20261021/s6-digest-roundtrip-targets.json`.
Exact per-target commands, source/revision/tool/import hashes, exit status,
wall time, RSS, swap and axioms are in its selected receipts. The transitive
object hashes are in `s6-digest-roundtrip-import-pins.json`; no binaries are
committed. The audit command is:

    python3 -B tools/s6-full-forest-roundtrip-20261023/check-digest-roundtrip.py

Accepted focused targets all exited zero, used the atomic local Lean lock,
-j1 and -M4400, reported zero swap, and audited only propext, Classical.choice
and Quot.sound. No unchanged full replay ran. Earlier failed attempts and
probe outputs are excluded diagnostics; their recovery sorryAx reports are
not installed proofs. Reserved Lean identifiers were corrected in source;
all actual accepted statements are pinned by their current source hash.

Key receipts: digest inverse v1 14.083942s/2240135168B RSS;
common decode v4 13.250699s/2232270848B; byte-slice equality v3
6.860916s/2245935104B; header v8 9.061456s/2234580992B;
complete payment decoders v1 9.537085s/2246901760B; accepted payment frames
v3 16.961616s/2236366848B. All figures are measured focused checks.

## Remaining enclosing premises and next deliverable

- Complete payment accepted inverse: compose the actual source writer frames
  with the newly derived accepted decoder frames and validator replay.
- Snapshot, afterstate and enclosing full forest accepted inverse; complete
  decoder totality beyond the now-closed digest and payment boundaries.
- Contextual transport of the historical loop/reference transformations,
  actual runtime/allocation effects, and current first/first_decoded/owned
  stage1 caller and ordered trace port. No free SDK/source dictionary is
  claimed equal to the concrete instance by these codec results.
- S1 original native whole prepared_claim/Prepared caller with actual Std/P6
  interpretation. Existing same-gamma scratch and joint challenge provenance
  proofs remain valid within their recorded premises, not whole S1 closure.

S2 belongs to its transferred owner. Session A's current handoff records its
boundary theorem and the current stage-port targets. No other cone was edited.
Any candidate adoption still needs relevant equivalence and artifact/proof
re-pin gates; this checkpoint makes no new source-adoption decision.
