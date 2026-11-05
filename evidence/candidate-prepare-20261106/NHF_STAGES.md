# NHF staged prepare work

TX1:087 OPEN. Only CLOSED callees can be installed; table is a work inventory, not an admission certificate.

| Cut | Actual boundary and invariant | Packet status / work |
|---|---|---|
| S0 | heap filled(14759,0); same owned result; allocation Err maps to Error::Allocation; split at 13831 | NGC u8 n<=32768 covers allocation success/failure. NHF_Layout proves size bound and disjoint partition. Native association/frame chain pending. |
| S1 | expand_semantic(proof[16..7031],logical[0..13831]) | NGV_SemanticPacket.result constructs SAME output on input7015/output13831, with errors retained in step interfaces. Pending caller substitution. |
| S2 | expand_values(proof[7031..7495],logical[13831..14759]) | CLOSED NFU/NGV_ExpandAssociation.result: bytes464<=1856, aligned16, output928=2*464. Pending SAME allocation frame. |
| S3 | wide_view(proof,logical[..13831],logical[13831..]) | TX1:095 OPEN in NGZ, small unowned leaf attempted here. Decoder TX1:048 is CLOSED; actual decoder executes in NHF native checks. |
| S4 | verify_observed(public,v.semantic,hash,None); map every wire error to Semantic | TX1:137 OPEN. Large semantic chain is a boundary, not assumed. NFW local control fragments do not install a complete packet. |
| S5 | mark(None,Semantic); Prepared::new(&SAME sem,&SAME v,hash,SAME g) | TX1:179 OPEN; NGN records incomplete scalar/queries/prepared_claim provenance. Owner's other workers own these packets; no duplicate proof. Returned Box and scratch effects must include constructor failure. |

The current frozen source is pinned in NHF_FROZEN_SOURCE_PINS.json and scratch-only changes in NHF_native.patch. KMX patch hash bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No function contracts or field-product stubs are introduced by the initial wide-view checks. NHF_K001 was an input-name error before verification (missing verifier:: prefix), corrected at K002; no harness was renamed to obtain a verdict.
