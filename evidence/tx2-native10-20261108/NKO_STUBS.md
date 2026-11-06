# NKO stubs and oracle boundaries

No field multiplication is executed or proved in Kani. No field arithmetic stub, writable static, or function-pointer-dependent observation is introduced. Ruling (t) fidelity calibration passes for the slice/metadata/Unit and richer borrowed query/metadata/Unit shapes. K038/K039 plus K040--K042, and independently K044/K045 plus K046--K048, provide all required controls. K050/K051 revalidates the richer contract after adding byte-frame observations. K049 detects even an out-of-frame write restored before return. K036 is a compiler ICE, not a passing control. K043 owned-return contract is timed out and retired; that shape is NOT admitted.

Every Kani run applies exactly KMX_copy_stubs.patch, SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. The two enabled replacements are core::ptr::copy_nonoverlapping -> KMX_copy_nonoverlapping and [u8]::copy_from_slice -> KMX_copy_from_slice. Safe input construction supplies their Copy/length/non-overlap conditions; matched falsifying controls use the same replacements. KMX value laws remain the retained KMX_CopyMeaning packet; no custom copy stub exists.

Child boundaries use LOCAL mutable typed records. C03 decode returns arbitrary Option<E> with every raw limb unrestricted. Pending and finish return every Rust Error or full successful carrier. Incoming query windows stop at the callee entry after checking arguments; they assert no returning property. Return/destructure and cleanup must be supplied separately. No generic callback or free child endpoint is admitted at a positive root.

The field-multiplication (stub, Lean theorem, domain) table is empty: no such stub is used. Existing CLOSED child packets are applied at SAME source arguments; their retained tool/runtime trust is P6/D188 option-A reclassification, not removal and not new trust.

| Replacement / abstraction | Paired law or evidence | Domain / scope |
|---|---|---|
| KMX_copy_nonoverlapping; KMX_copy_from_slice | Exact retained KMX patch and KMX_CopyMeaning value laws; every credited native pair has same-config failing control | Safe typed constructors; exact counts; nonoverlap; no custom replacement |
| stub_verified(NKO_QueryFrame.full) | K050/K051; K046/K047/K048 fidelity controls; K052/K053 byte observation; NKO_ReadonlyFrame.view_frame, NKO_FrameG.proof_source | Incoming borrowed proof/p/a/g/geometry/pending, log.calls=0; only local Log may be modified; immutable live regions disjoint |
| Incoming query child boundary | K010--K015 and retained NKE/NJR cuts; full typed input carriers | Entry only; no returning/drop claim from assume(false) |
| Owned query child reply | K056--K059 direct execution; NKO_QueryReturnG.full_result, retained_return | Arbitrary full Result, all input carriers; borrowed proof unchanged; output ownership descriptors/scalars; retained NJR payload/drop obligations still explicit |

The native contracts are explicit P6/D188 option-A semantic-transport reclassification. No trust item is removed. No field multiplication stub is used, so the requested multiplication (stub, Lean theorem, domain) table has zero rows. Native before/after byte preservation is checked directly in K052--K057, rather than inferred from integer pointer metadata alone.
