# Same original frame implies the same actual and typed polynomial

Successful typed semantic-row decoding of the actual source record frame now supplies the retained coefficient decoder on exactly that frame's payload. The constructor identity is the existing SemanticPayloadView.coeffAt_payload fact, rather than a new polynomial-equality assumption. Composing this with actual decodeMain success proves equality of the actual polynomial mapped into WideExact and the typed polynomial. Payload equality, payload length, strict low-chunk validity, individual field values and polynomial equality are all derived.

The source caller still must identify the same parsed typed row/accepted frame, and supply actual run and transcript provenance. This packet closes the whole-frame decoder-to-polynomial bridge, not all semantic Checks or complete spend soundness.

The four focused Lean 4.32 checks exited 0 in 1.19, 7.39, 7.07 and 18.34 seconds. Peak RSS was at most 3,229,630,464 bytes, zero process swaps; all printed theorem axioms are standard. Exact source/object/import hashes, source revision, commands and logs are retained.

The first combined proof exceeded the interpreter memory guard (54.47 seconds, 3,742,679,040 bytes); a split proof still exceeded it (58.54 seconds, 3,742,826,496 bytes). A 20,000-heartbeat diagnostic isolated kernel reduction (16.96 seconds, 3,070,214,144 bytes). The replacement proves the arbitrary-payload header-drop identity once using List.drop_left', retains it as an opaque named theorem, and composes equalities without reducing a concrete coefficient encoding. The successful same-frame consumer uses these small helpers under the original memory cap. Representative failed source/receipts/logs and the replacement are retained; no failed target is claimed accepted.

The unchanged R1SemanticRecordCodec object is reused from the recorded 2026-10-16 check, with matching exact source/object hashes and a source-alias record. No dependency rebuild or full manifest replay was performed. This is focused working evidence under the research-branch release policy.
