# Replacement inventory

No field multiplication replacement was used by an NDD native proof. No variable-by-variable field multiplication was verified in Kani. Existing LPh emitted multiplication value laws remain reusable but were not converted into unpaired NDD stubs. Constant two-fold linear scales in the pack arithmetic spans are ordinary bounded u64 arithmetic.

| Replacement | Pairing / domain | Disposition |
|---|---|---|
| `kani::stub_verified(M31::reduce_u64)` | K062 actual contract PASS; K063 inverted target postcondition FAIL. Exact two-fold Rust reference; `NDD_ChannelPrimitives.reduce` associates its extracted definition to FIq M31::reduce_u64 on all U64 inputs. | Used only in excluded packing shapes K066/K067. K066 was codegen failure before adding the cfg(kani) Arbitrary impl; K067 timed out. No caller closure credit. |
| Exact KMX copy replacements | Patch SHA256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`; immutable files checked before every run. K060/K061 one arbitrary QM31 copy window and frame; `NDD_CopyFrame` uses `KMX_CopyMeaning.loop_spec/copy_frame`. K080 negative pointer-copy control fails under deployed verifier features. | Local copy/value evidence only. Pointer validity, non-overlap, exact lengths, SAME allocation/caller association and surrounding runtime remain obligations. |
| `NDD_weights::decode_cut` for WideExact::from_le_bytes | K076/K077; exact 32-byte selected input and unchanged Some reply. `NDD_SelectorModel.field_cut` exposes the same abstract decoder success premise. | OPEN: diagnostic source envelope is 64 bytes and i<2; this is not established for the real callers and is not a real decoder value/success bridge. |
| Static digest `Recorder` | K056–K059 check exact tag and ordered slices plus unchanged arbitrary reply. | Not a SHA replacement or value law. Actual enclosing model/dictionary/effect/caller association remains OPEN. RuntimeSha256Value remains separate trust. |

Scalar, array32 and nested-array9 interface controls are K041–K055. Every inverted ensures failed; real bodies passed while unimplied assertions failed under stub_verified; forbidden writes were detected by modifies checks. No function-pointer or Option<fn> observer carries these properties.
