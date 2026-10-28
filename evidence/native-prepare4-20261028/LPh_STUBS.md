# NCA native replacements and exact domains

No field multiplication is executed or newly stubbed here. Existing arithmetic pairings are imported from NBA/NBL/NBR and the CLOSED leaf packets, not re-proved. A missing native callee association remains OPEN.

| Replacement | Lean pairing | Caller domain / evidence |
|---|---|---|
| unchanged KMX_copy_from_slice / copy_nonoverlapping | KMX_CopyMeaning.copy_prefix/copy_frame; NCA_SerializerWindow.frame | initialized, valid, disjoint arrays/slices, matching four-byte lengths; safe native borrows and index<8. Exact supplied patch sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. K002/K003 and K004/K005 positive/failing-control pairs. |
| NCA_serialize_cut | NCA_InactiveModel.source/words; NCA_InactiveDomain.source | actual Prepared::new mode0 reaches same inactive after gamma; K006 argument position PASS/K058 forced ONE-vs-ZERO control FAIL. Cut stops, fabricates no result. Complete value law comes from native zip step plus existing Lean induction. |
| NCA_scalar (source-position overapproximation) | NBR_BlockConstruct.scalar, NBR_OpeningConstruct.source and inherited NBL scalar ports | exact row/nonzero/payload/preceding-state routing checked by K006; no scalar arithmetic refinement claimed from this overapproximation. Actual callee bridge must compose. |
| NCA_Digest (source-position overapproximation) | NBR_BlockConstruct.Total D / U00 NBR_NativeDigestRequests | exact salted seed byte requests and replies; no digest-value realization or totality derived from Rust return type. Runtime dependency retained. |

KMX_clone_from_slice/to_vec/realloc are present unchanged in the included supplied patch; only reached and paired uses receive credit. No KMX_extend replacement is used by the mode0 prefix (append cut unreachable there). Domains involving live allocation ownership remain U00 obligations.


| Additional replacement | Lean pairing / exact status | Domain |
|---|---|---|
| NCA_Parser::parse | NCA_ObservedControl.parse_error/public_error/begin_error/finish_result reuses the exact VerifyPrefix control definition; actual parser native/model bridge OPEN | same borrowed semantic13831 carrier and root/record offsets; returns typed arbitrary error or Prefix |
| NCA_public | same control theorems; actual public-transcript bridge OPEN | exact public variant/pointers, digest argument and parsed root; arbitrary child Result, no arithmetic identity assumed |
| NCA_begin | same control theorems; actual begin bridge OPEN | same Prefix, transcript successor and every Challenges field checked; arbitrary child Result |
| NCA_finish | NCA_ObservedControl.finish_result, NCA_ObserverErasure.finish/source; actual FinishModel bridge OPEN | exact public, Prefix, transcript/challenges; default no-detail-phases observer is irrelevant; complete Verified return fields retained |
| NCA root/round append cuts | NBR_AppendInduction.step/prefix_step/capacity and NCA_AppendDomain.source | returned producer lengths32/224 and live Vec capacity256; source-position overapproximation only until native step and lifetime association compose |

These call-routing replacements are explicitly OPEN lower native obligations, rather than discharged semantic stubs. They never provide native credit for a callee. No field multiplication replacement was introduced. KMX source and natural-value laws remain unchanged. KMX allocation/reallocation correspondence and ownership are not implied by a byte-value proof.

Native returned-claim constructor K065/K066 pairs with NBR_PrepareConstruct.source and the inherited complete Prepared field theorems, restricted to the same passed semantic/query/scalar/rho/claim/transcript carriers. Claim-result overapproximation is not a native prepared_claim bridge. Every actual callee use must compose its own established domain and mitigated bridge.
