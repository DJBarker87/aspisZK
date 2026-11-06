# NKK stubs, contracts and domains

No field multiplication is proved in Kani. No field multiplication stub was added. No function-pointer/Option<fn> or writable-static proof credit is used.

| Mechanism | Domain / paired law | Evidence |
|---|---|---|
| Exact KMX copy stubs | Supplied KMX patch sha256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`; retained KMX_CopyMeaning/value laws | Every copy-dependent component has a failing control in the same configuration; NKK_NATIVE_CERTIFICATES.json |
| RawOracle::raw | N=4/32; immutable 1768-byte backing, full raw reply and arbitrary post-cursor | CLOSED NJZ_Readers.raw_cut at SAME arguments; NKK_RawSlots/RawPrefix/RawCps and source clauses; overall parent installation remains OPEN |
| k/e opaque child replies | Native caller receives the full flat decoder reply, reader cursor and frame | CLOSED NJZ_Readers.k/e in their N16/32 domains; NKK_ReadFrames, DecoderDomain, FieldDomain/Association/Sites; no multiplication |
| proof_digest_frame_cut contract | borrowed proof57607, stored32, fixed-array reply32; Result<Unit,Error>; exact modifies protects complete input/reply bytes | K042 positive; K046 inverted ensures FAIL; K047 modifies violation FAIL; K050 wrong argument FAIL. Borrowed-slice/record/Result shape calibration K032/037/038/039/040/041: inverted ensures fails; unimplied caller assertion passes real body and fails stub_verified; modifies violation detected. NKK_DigestCut is the typed semantic transcription, not an unconditional native-parent theorem. |

Native contract semantic transport is the owner's option-A P6/D188 tool-trust reclassification, not removal and not a new trust item. Runtime digest values remain the existing sha256=H realization row: native cuts prove exact ordered slices and unchanged returned replies only.

Frozen graph is validated before every native attempt, offline; Cargo.lock unchanged checked afterwards. CARGO_TARGET_DIR is own NKK_target. Scratch harness patch is NKK_native.patch; exact KMX patch is separate. All receipts retain their original failing/timeout verdicts.
