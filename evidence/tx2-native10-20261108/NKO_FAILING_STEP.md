# NKO failing steps

K001: input harness called nonexistent QM31::new (E0599); no verification ran. Fixed to the actual public raw-word constructors, preserving arbitrary words. K002 is the corrected source, same harness name and property. No timed-out shape retried.

K002: CBMC 90s timeout on inactive payload plus arbitrary whole-proof byte-frame observation (57607-way index). RETIRED. K003 removes that independent whole-proof frame mux; C03 payload/result only, frame remains an explicit separate obligation. Same harness name retained. No cap/timeout increase.

L004: PSem_Slices selects an incompatible historical Phase owner in the combined cohort. Removed that extra import; C03 now proves the concrete range directly over the already loaded pinned Aeneas index definition. This is an own-source import correction, not a shared-cache repair.

K018: C07 whole57607-byte incoming payload observation exceeded the unchanged90s CBMC limit; RETIRED, no credit. Replacement: eight disjoint8192-byte (last263-byte) projections on the SAME typed full arbitrary input. Each gets a fresh matched control and Lean quotient/remainder coverage, never a rerun of the full shape.

NKO_K019: verifier::candidate::NKO_parent::query_proof_block0 did not pass; NKO_K020 NOT launched. Retain exact log and isolate rather than rerun unchanged.

NKO_K021: verifier::candidate::NKO_parent::query_proof_block1 did not pass; NKO_K022 NOT launched. Retain exact log and isolate rather than rerun unchanged.

NKO_K023: verifier::candidate::NKO_parent::query_proof_block2 did not pass; NKO_K024 NOT launched. Retain exact log and isolate rather than rerun unchanged.

NKO_K025: verifier::candidate::NKO_parent::query_proof_block3 did not pass; NKO_K026 NOT launched. Retain exact log and isolate rather than rerun unchanged.

NKO_K027: verifier::candidate::NKO_parent::query_proof_block4 did not pass; NKO_K028 NOT launched. Retain exact log and isolate rather than rerun unchanged.

NKO_K029: verifier::candidate::NKO_parent::query_proof_block5 did not pass; NKO_K030 NOT launched. Retain exact log and isolate rather than rerun unchanged.

NKO_K031: verifier::candidate::NKO_parent::query_proof_block6 did not pass; NKO_K032 NOT launched. Retain exact log and isolate rather than rerun unchanged.

NKO_K033: verifier::candidate::NKO_parent::query_proof_block7 did not pass; NKO_K034 NOT launched. Retain exact log and isolate rather than rerun unchanged.

K019/K021/K023/K025: distinct8KiB blocks0–3 each timed out at90s; no credit. The original serial batch had already advanced through distinct block arguments before the failure was handled; it was held and all later unlaunched slots remain unused. Future batches stop on the first failed shape. No target is resubmitted unchanged.
Replacement isolates the unrelated input-construction loops: C07's input factory bitcasts nondeterministic raw u32 arrays to the all-bit-pattern-valid M31/QM31/WideExact fixed arrays, then uses the same Vec::from with exact KMX. No zero/sparse cell, canonicality restriction, source-body substitution, custom copy stub, cap/timeout increase or new tool trust. All these field carriers contain only u32 newtypes/records; Rust compile-time transmute size checks apply. Expected weights are read from the typed PRE-state, so no field-layout ordering is assumed. Every original well-formed raw input remains representable. Fresh block7 preflight comes first, then the retired block0 property with this changed generator.

L085: final C09 source installation hit default recursion depth while normalizing literal range differences inside a large local context. Split concrete ranges into NKO_ViewRanges with named omega arithmetic facts before installation; no maxRecDepth/maxHeartbeats change.

K033/K034 positive/inverted-ensures and K035 real-tag and K037 modifies-violation have expected verdicts, but K036 stub_verified calibration NEVER verified: Kani ICE resolving missing Arbitrary<ProofLog>. This family earns NO admission. Replace the logging record's raw address metadata with scalar usize metadata and derive Arbitrary; the actual borrowed slice remains typed and unchanged. Addresses are observations only, never a pointer-to-payload implication or a fabricated typed reference. Re-run the entire changed shape's controls. No renamed harness or altered security proposition; new source/hash and same harness names.

K043: full owned-input/owned-reply discard contract timed out at90s; RETIRED. Split its incoming borrowed argument frame from owned transfer/Result/drop, already checked by K010--K015 and retained NJR cuts. New shape has all SAME Prepared/Accumulator/powers/geometry/pending payloads, borrowed only during entry capture; no Result seed or drop loop in this projection. Calibrate this distinct interface before using it.

The owned query alternative isolates two observations: a before/after byte on the SAME proof and the returned full Result descriptors/scalars. It executes the literal owned call/destructure with arbitrary successful or error child reply and full arbitrary input carriers, without contract instrumentation; it does not replay K043 or assert allocator event semantics. These remain native window candidates until their source association is installed.

Final-source fidelity review: after K049, the QueryFrame source gained independently checked owned-call payload/Result harnesses (K056--K059). The last native slot is reserved for the restored out-of-frame write control on that changed final source. This is a focused negative fidelity check after a source change, not a replay of a timeout, not an extra positive contract admission and not additional row credit. The earlier per-shape positive/control families remain pinned in their exact source capsules.
