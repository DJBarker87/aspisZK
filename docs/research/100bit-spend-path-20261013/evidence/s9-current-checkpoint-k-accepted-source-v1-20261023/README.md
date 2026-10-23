# Current checkpoint K decoder: accepted source transport

This packet interprets the exact current Rust `QM31::from_le_bytes` cut on a successful output, and its explicit Reader.k-shaped adapter. The format is the full 16-byte checkpoint field; this is not the compact proof-buffer codec.

The extraction uses byte-identical current field, circle and wide-exact inputs, no opaque paths or function-body substitutions, and the retained R72 Charon/Aeneas toolchain. Both stages ran inside one admitted 2 GiB Linux scope with swap prohibited. Generated resource-option declarations were removed; the concrete existing `DecodeKOptionDiscriminantBridge` import was added after the first owner compile exposed a missing Option<Infallible> discriminant instance. Generated definitions otherwise remain unchanged.

Proved claims:

- `CMMap.cm_decoder_map`: complete Result mapping for the current CM decoder, including failures, divergence and None.
- `Accepted.qm_success_to_old`: an actual successful current QM decoder call implies the retained decoder succeeds on those same bytes with the same four words under nominal carrier copying.
- `Accepted.current_decoder_success_canonical`: that same current successful output has all four words strictly below the field modulus. The retained FullV10 canonicality theorem is reused; no decoder-correctness premise is assumed.
- `ReaderAccepted.actual_decoder_success_retained`: accepted same-value transfer for the stage-2 carrier adapter.
- `ReaderAccepted.readerKCurrent_success_retained`: a successful current-shaped reader call implies retained-reader success with the same output and cursor.
- `ReaderAccepted.readerKCurrent_success_canonical`: consequently its output is canonical.

These accepted-run claims do not assert equality of rejected executions. The unsuccessful full-QM-result mapping attempts are retained in history and remain OPEN. Since this decoder is pure and has no oracle interactions, accepted same-value/cursor transfer is sufficient for its local canonicality use. A transport proof for an adaptive security experiment is not claimed here.

The actual Reader raw-byte operation, its caller/runtime adoption, complete resume-source refinement and the composed soundness theorem remain OPEN. Earlier semantic-alpha/z producer results used the retained strict reader. This packet supplies the current decoder accepted interface needed to replace that old decoder boundary; it does not silently claim that replacement has already been composed into every caller. Whole S9, R22 totality and the 100-bit target are not established by this packet.
