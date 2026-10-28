# NCA native replacements and exact domains

No field multiplication is executed or newly stubbed here. Existing arithmetic pairings are imported from NBA/NBL/NBR and the CLOSED leaf packets, not re-proved. A missing native callee association remains OPEN.

| Replacement | Lean pairing | Caller domain / evidence |
|---|---|---|
| unchanged KMX_copy_from_slice / copy_nonoverlapping | KMX_CopyMeaning.copy_prefix/copy_frame; NCA_SerializerWindow.frame | initialized, valid, disjoint arrays/slices, matching four-byte lengths; safe native borrows and index<8. Exact supplied patch sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. K002/K003 and K004/K005 positive/failing-control pairs. |
| NCA_serialize_cut | NCA_InactiveModel.source/words; NCA_InactiveDomain.source | actual Prepared::new mode0 reaches same inactive after gamma; K006 argument position PASS/K007 negated control FAIL. Cut stops, fabricates no result. Complete value law comes from native zip step plus existing Lean induction. |
| NCA_scalar (source-position overapproximation) | NBR_BlockConstruct.scalar, NBR_OpeningConstruct.source and inherited NBL scalar ports | exact row/nonzero/payload/preceding-state routing checked by K006; no scalar arithmetic refinement claimed from this overapproximation. Actual callee bridge must compose. |
| NCA_Digest (source-position overapproximation) | NBR_BlockConstruct.Total D / U00 NBR_NativeDigestRequests | exact salted seed byte requests and replies; no digest-value realization or totality derived from Rust return type. Runtime dependency retained. |

KMX_clone_from_slice/to_vec/realloc are present unchanged in the included supplied patch; only reached and paired uses receive credit. No KMX_extend replacement is used by the mode0 prefix (append cut unreachable there). Domains involving live allocation ownership remain U00 obligations.
