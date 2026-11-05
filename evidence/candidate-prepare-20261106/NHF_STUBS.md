# Substitutions and exact domains

No field multiplication, function pointer, Option<fn>, proof_for_contract or stub_verified is used by any selected NHF gate. Ruling(t)'s extra contract-shape controls are consequently not invoked. No unpaired field stub exists.

| Substitution | Compiled law and exact caller domain | Status |
|---|---|---|
| Prescribed KMX copy stubs | Exact KMX_copy_stubs.patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; original KMX value laws, NHF byte/record associations; valid disjoint source/destination for copies | K020/K021 copy32 and K088/K089 actual E-record positive/intended-failure pairs; no custom copy implementation |
| Heap boundary local log | NGC complete heap::filled TX1:064, u8/n14759<=32768, effect-free clone, SAME reservation outcome and owned Vec; NHF_HeapPrefix.outcome/success_domain/rejection_frame invoke the identical filled_exact law | K007/K008 partial cut; complete callee supplied by NGC; no allocator-success assumption |
| Semantic expansion local log | NGV_SemanticPacket.result, SAME original7015 bytes and actual13831 output; NHF_StageObservations.semantic/original_byte, NHF_ScalarWindow.read/represent | K009/K010 frame and K030..K085 prefix/row logging pairs; complete physical writes supplied by CLOSED callee, never inferred from a single post-byte |
| Values expansion local log | NGV_ExpandAssociation.result; SAME original464 input, actual928 output, alignment16,464<=1856; NHF_Expansions/NHF_Overwrite/NHF_Prefix | K011/K012 frame and K086/K087 logging pair; actual Vec back-functions by NHF_Recombine |
| WideExact::from_le_bytes local log | CLOSED NET TX1:048/TX2:031; NHF_ViewDecoder.result from UnrolledWideParserRefinement.source_refines; same original proof[7495..7527],32 bytes; all8 natural u32 words, Some exact limbs iff all<P, otherwise None | K018/K019, K022/K023, K025/K026 full-law cuts; callee domain derived from original proof57607. Both Some/None covered. No canonicality/success/desired-output premise |
| Semantic verifier | Complete TX1:137 callee packet unavailable | OPEN; no stub admitted or assumed |
| Prepared::new | Complete TX1:179 sampler/query/native provenance packet unavailable | OPEN; no stub admitted or assumed |

K005/K006 were early overapproximating decoder cuts and are not selected for final leaf credit. K024's assertion-format failure is diagnostic only; K026's single failure maps to the explicit decoded-reply assertion at archived source line50. All timeout/unwinding/parent-limit shapes are excluded. Logging stubs change only local log records; their complete child content laws come from the named CLOSED packets. Native semantic transport remains retained P6/D188 trust, a reclassification rather than removal.
