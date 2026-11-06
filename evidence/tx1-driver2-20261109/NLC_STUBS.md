# NLC stubs and fidelity

No field multiplication stub or multiplication proof was used in Kani. No new LPh_STUBS field entry is submitted. The interpreter's multiply arm is still missing its native association and caller-domain installation; existing JFv/Lean field laws are not replaced.

All native harnesses use exactly KMX_copy_stubs.patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Its unchanged copy_nonoverlapping stub is paired with KMX_CopyMeaning.loop_spec/copy_frame, and NLC_CopyFrames supplies symbolic window/disjointness composition. Pointer validity, actual layout, ownership and caller domains remain external obligations, never inferred from value laws. Every positive has its assertion-failing control in the same configuration.

No proof_for_contract, stub_verified, Option<fn>-dependent assertion, writable static or new runtime trust item. Constructor Hash(u64)::digest panics if called; no digest/SHA call is reached. Generic/deployed hash-carrier association is OPEN, so these local constructor windows are not whole deployed-parent credit. The scalar terminal-map window has no hash carrier.

K004 aggregate constructor timeout is retired; eight field properties are strict splits, not renamed repeats of its property. K001's own module-path compile failure was corrected with explicit cfg-only path attributes. All frozen graphs and post-run lock checks are retained. No source or Cargo.lock drift was found.
