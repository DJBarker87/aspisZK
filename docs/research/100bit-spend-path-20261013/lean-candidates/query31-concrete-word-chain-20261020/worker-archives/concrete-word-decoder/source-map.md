# Query31 concrete block-word decoder

This is a focused proof packet, not a deployment or end-to-end source-equivalence claim.

The pinned Rust source is `crates/aspis-core/src/r0_transcript.rs` at commit `27f484a88`; its full-file SHA-256 is `2a315219d20069742c7c07e2a1ab8ee283865be3c607fdde2cf6975ad1813fc1`. The retained QueryScan source pins repeat this exact file hash and identify `QUERY_BOUND` at lines 47–48, `block_rank` at lines 89–94, and `query_words` at lines 186–188. The generated Funs reference is SHA-256 `2c12496051a1530e35d24d133bf6341f0995a43e0fc39a446250892afcc2a42f`; it is included as a source reference only and is not imported by either accepted Lean target.

`QueryScanConcreteWordsDecoder.query_words_success_byte_mask` proves that a successful 32-byte query-block parse produces, in index order, each four-byte little-endian word masked by `QUERY_BOUND - 1 = 262143`. The callback uses four checked array reads and `U32.from_le_bytes`; `block_rank_success_words_in_order` derives the 8 outputs from the checked `arrayFromFnLoop` model. The follow-on theorem proves the array-map output order using the existing Aeneas array-map model and its success theorem.

`Query31ConcreteWordsDriverChain.successful_driver_has_concrete_q22_chain` instantiates the previously checked first-stop Q22 driver chain with this actual query-word decoder. Every evidence item retains its same selected `bytes`, successful decoder output, and Q22 scan call, so the byte-mask theorem applies to the exact block associated with that transition; the previous arbitrary `decodeBlock` backend is no longer needed for this consumer.

The new library-construction boundary is Rust `core::array::from_fn`, modeled by the option-free `TerminalArrayFromFnModelV4Clean` owner. The array-map model is an already checked Aeneas standard-operation owner. This packet does not establish a new general Rust standard-library theorem for `from_fn`; it records that boundary explicitly. The rest of the extracted callback and query mask proof has no external-function axioms. Both checked target theorem audits list only `[propext, Classical.choice, Quot.sound]`.

No `FunsExternal`, `Funs`, `maxHeartbeats`, `maxRecDepth`, `native_decide`, or custom `axiom` declaration is imported or used by the two accepted targets. Model/driver sources are references only where noted. Object files are intentionally not included; exact object hashes and native cache paths are recorded in `manifest.json` and the captured preflight receipts.
