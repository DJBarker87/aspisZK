# Opacity plan and extraction provenance

E001 targets the byte-identical frozen candidate::prepare. The scratch crate has the frozen Cargo.lock. No source attribute, body, wrapper, or compiler/tool patch supplies opacity.

`--opaque crate::verifier::_` covers the inherent Prepared impl as well as all verifier helpers; the more specific `--include crate::verifier::candidate::prepare` exposes the target. Explicit includes expose the data carriers Prepared/View/Phase/Error/Accumulator/QueryGeometry, without including their impl methods. This replaces NHF's failed `crate::verifier::Prepared::new` pattern; NHF's diagnosed id14 was Transparent.

Other option boundaries: r1_semantic and r1_wire children (existing packet chain; verify_observed remains OPEN); field/circle methods (existing field/writer packets, no multiplication extraction here); heap::filled (NGC packet); compact::expand_semantic and expand_values (NGV/NFU packets); weights methods and transport methods (not part of the parent body). The exact list and tool digests are in NHL_EXTRACTION_PINS.json. Any reached OPEN child is a theorem hypothesis, never an assumed successful result.

No retained full tx1 emission was found: NFW's pinned emission is tx1_split_ref, a scalar control helper. E002 is therefore reserved for actual tx1 with its callees opaque, including prepare. Every fresh LLBC is inspected for target Structured / constructor Opaque before relying on the Aeneas output. Raw templates with placeholder axioms are evidence only, never imported into a proof.
