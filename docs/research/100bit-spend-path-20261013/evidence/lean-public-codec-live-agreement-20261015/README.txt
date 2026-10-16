PUBLIC CODEC / LIVE CHECKED PARSER AGREEMENT
Prepared 2026-10-16; task and retained artifact suffix 20261015.
Base b8760b76ac8de6c5c903eb98ff3a85f6f9f532e8.
Target: R1PublicCodecAgreement, canonical source
  docs/research/100bit-spend-path-20261013/lean/PublicCodecAgreement.lean.

SCOPE
Extends the existing module; both original public declarations are preserved.
No codec definition, source serializer, or live consumer is changed.
BasePublic is R0P.Public M31Exact. Encoding is defined exactly when nextPairIndex
is below 2^64; malformed options and zero withdrawals are not encoder guards.
For every public value and bytes, parsePublic bytes = some pub iff
PublicByteCodec.encode pub = some bytes AND PublicOptionShape.canonical pub.
For every byte list, PublicByteCodec.decode bytes = SemanticPublicWire.parsePublic
bytes, including malformed/truncated/trailing input. Raw SemanticPublicWire.decode
is deliberately not equated with the checked decoder: it accepts the symbolic
zero-withdrawal wire, while both checked parsers reject that wire's bytes.

EXACT LIVE HYPOTHESIS
PublicCodecAgreement.parsePublic_of_decode bytes pub h discharges
  SemanticPublicWire.parsePublic bytes = some pub
from h : PublicByteCodec.decode bytes = some pub, with no new premises.
The caller's actual source execution/validation, omitted-metadata bindings,
and the separately extracted Lean4.31 modules' Lean4.32 integration are not
proved by this representation bridge.

CACHE / REPLAY BOUNDARY
cache-pins.json pins all 20 project imports in the transitive closure and the
changed target. Imported source bytes equal revision
7c5ca86991e45c33f3eb7b34cd34ccda5e71d620; existing source-verified retained Lean4.32
objects were reused and their hashes re-observed. No dependency was rebuilt.
Runtime pins record the actual Lean4.32.0 executable/dylibs and current lake
manifest. External Mathlib cache provenance remains that pinned workspace's
retained cache; this bundle is not a self-contained distribution of Mathlib.
run-lean.py is the exact local bounded runner, retaining absolute environment
paths in each receipt; lean-with-cache.py is the exact invoked wrapper.
Replaying requires those pinned caches/workspace, or independently reconstructed
compatible caches. A source hash alone is not a source-to-object proof.

FAILED ATTEMPT
failed-codec-a preserves the first source, cache pins, complete log and receipt.
It failed only because broad simp normalized 2^64 inconsistently in
encode_none_iff. Its sorryAx diagnostic is failed-check evidence, not a theorem
claim. The replacement uses explicit case constructors and contradiction;
no reduction-limit increase or larger memory cap was used.

FINAL CHECK
codec-b: exit 0, 18.339 seconds, sampled aggregate RSS 3,450,240 KiB;
process maxRSS 2,902,212,608 bytes, zero process swaps, system swap unchanged.
Exact command and memory/time guards are in codec-b.json and run-lean.py.
All ten public theorem audits use only propext, Classical.choice and Quot.sound.
Three inherited unused-simp warnings are retained; existing proofs were unchanged.
The final source and its new .olean are included, independently hashed.
No unchanged green target was rerun. No package-wide or host build was run.
