Actual ASQ8 reconstruction to live parsePublic, Lean 4.32

The three new proof modules consume C's committed exact reconstruction result
e97ac2bb0275bea5f4f73cdcbb064d45d03df9cd and the checked Caller/public chain at
be46d779069c062b198ed4e57f3c3e4860ab878b. No production source is changed.

ExtractedAdapterWithdrawalSuccess inverts the actual terminal validator prefix:
successful Withdrawal validation implies successful ASWP encoding on that same
public. ExtractedAdapterCallerBridge copies all nine withdrawal fields, proves
both carrier roundtrips, and proves equality of the actual payment validator and
encoder outcomes (including returned bytes), with an explicit error map.

ExtractedAdapterPublicBridge.reconstruct_encoder_success takes the exact request
Withdrawal payload and actual reconstruct_asq8_statement success. It derives the
actual Caller encoder success; no nested validator or payment success is assumed.
reconstruct_serializer_parsePublic additionally takes actual semantic public_bytes
success on that same fixed public and a transition copying all six live_snapshot
fields and all three candidate fields. It yields the fixed PublicSourceRaw.toWire
equation and live SemanticPublicWire.parsePublic on the exact serialized bytes.
reconstruct_serializer_supplied_public retains the exact wire projection equation
and supplied = SemanticPublicWire.toPublic wire equality required for live hpub.

The joint import exposed the payment Error's unqualified discriminant instance.
The one-sided Adapter Types overlay changes only its generated instance identity:
the same fourteen-code read_discriminant is explicit and the instance qualified.
rust_type and every other attribute are preserved. The inverse reconstructs every
original emitted byte. Original and adapted definition/constructor audit logs are
byte-identical: 80c3bf4f3f84d4ae45cda1ab453c73d6b4ff1a0ab219643d71dfbd80f3bc1067.
Original generated sources and caches remain untouched. This adapter is not a
new axiom or a replacement validator specification.

Nine affected targets passed first checks after the naming adapter. All 24
requested adapted reports (including the four actual reconstruction functions)
and the original constructor audit use only propext, Classical.choice, Quot.sound.
The final target took 2.412 s, peak process RSS 3,847,112 KiB, sampled cgroup peak
728,477,696 B, zero process/cgroup swap. Each target ran serially under explicit
6 GiB high / 8 GiB max / swap 0. The 46 unchanged imported project modules retain
their exact source/runtime/import/object receipts; only the four original
Adapter modules were removed and replaced by separately checked overlay targets.
No unchanged backend/public dependency replay occurred.

The archive retains the failed joint import, a prior pre-Lean snapshot root-alias
failure, both tag audits, staged sources, manifests, runtime/import/object pins,
namespace-link journals, every target receipt, and the final object. All 122
archive members and final source/object hashes were independently checked locally.
The inspected helper-body namespace normalization is evidence only; the checked
proofs refer to actual extracted definitions.

Open: actual serializer success at runtime; supplied-public equality; request
admission; account authentication producing the structural input; candidate/proof
decoding and reencoding; checkpoint provenance and proof/public hash binding.
The serializer is invoked on the stage1 path (r1_semantic.rs:74); ASQ8 stage2
encodes reconstructed ASF8 and calls tx2_authenticated without invoking that
serializer. This result does not derive stage1 success from stage2 reconstruction,
or prove authentication from the name AuthenticatedAsq8Accounts. Rust/extraction
tool correctness remains separate. See the source-pinned caller inventory in the
archive for exact paths, line locations and hashes.
