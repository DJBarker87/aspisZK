# NBR stub pairings and domains

No new field-multiplication stub or Kani multiplication proof is introduced. The inherited NBA/NBL sampling, powers and prepared_claim ports retain their named Lean arithmetic pairings in evidence/native-prepare2-20261027/LPh_STUBS.md and its cited leaf packets. Suspended prepared_claim remains conditional; no inherited LPb native credit is restored here. Natural producer domains are derived by NBR_ValuesPort, NBR_ProducerBuffers, NBL_ViewDomains and NBR_PrepareTotal rather than supplied canonicality flags.

## Newly used copy replacements

NBR_COPY_IMPORT.json pins merged research b173d5111cab35fe169da8c9942872071d04213a, KMX patch and exact prefix-only renaming. The unchanged proved KMX_CopyMeaning dependency was built once into the persistent cache (L027). KMX_K008 expected/wrong controls and KMX_R002 optimized native differentials are reused, within their documented limits. These value laws are not an axiom or a complete Rust-to-Lean refinement.

| Stub (NBR_ prefix) | Named Lean value theorem | Required domain / current caller proof |
|---|---|---|
| copy_nonoverlapping | KMX_CopyMeaning.loop_spec, copy_frame | T:Copy; initialized/aligned/nonoverlapping valid source/destination, count within allocation. Harness inputs are separate initialized arrays; runtime caller ownership stays NBC's explicit dependency. |
| copy_from_slice | KMX_CopyMeaning.copy_prefix, copy_frame | Matching lengths, T:Copy, safe disjoint slices. K002 geometry and K011 windows establish exact semantic header/payload slices. |
| clone_from_slice | KMX_CopyMeaning.copy_prefix, copy_frame | T:Copy only, so no Clone side effects; matching lengths. No new clone-dependent caller credit without reached-domain evidence. |
| extend_from_slice | KMX_CopyMeaning.append_spec; NBR_VecAppend.extend | T:Copy; live valid Vec, disjoint source; allocator ownership retained. Opening total size32+224=256 is derived by NBL_ViewDomains and NBR_OpeningConstruct. Capacity/address/allocation-count equality is not supplied by the value law. |
| to_vec | KMX_CopyMeaning.append_spec, copy_prefix | T:Copy, valid source slice; allocation ownership retained. No new reached use claimed yet. |
| realloc | KMX_CopyMeaning.realloc_prefix | Live owned allocation, valid old/new layouts, positive new size; MaybeUninit spare bytes. On failure old allocation retained. No native gate is allowed to assume allocator success beyond its source branch. |

## Callee cuts (not field arithmetic)

- NBR_check_values: K003 overapproximates complete child Results on the SAME464-byte proof range. Pair: CLOSED check_values leaf, LPt_LPl.Check.native_result; caller domain K003 pointer/length assertions. NBR_first_echeck terminates at the reached first child; it does not prove echeck or later scan completion.
- NBR_expand_cut: K005/K011 terminates at the actual expansion call, asserting SAME pointers, size<=1856, alignment and doubling. It invents no returned buffer. Pair: suspended expand_values leaf plus NBR_ValuesPort's complete same-buffer semantic slot association. No success from this cut is credited as a whole semantic row return.
- Native sampler/query/powers/claim cuts in reused NBL gates remain local control overapproximations. Every replacement use must compose with its closed/conditional callee on that callee's exact producer domain.

## Final producing-call and source-position cuts

| Cut | Scope / pairing | What the gate establishes |
|---|---|---|
| NBR_alloc / NBR_sem / NBR_y1 / NBR_view (K027/K028) | NativeFilled14759 and NativeSemanticLoop remain OPEN; model pairings NBR_ProducerBuffers.source, NBR_BufferJoin.source, NBR_ValuesPort.returned, NBR_SemanticReturn.returned | Exact source proof/ranges, one fresh allocation and order. Alloc returns arbitrary initialized bytes, producer success carries NO byte law; view cut terminates, fabricates no View. No complete native value closure credit. |
| NBR_payload_cut (K029) | KMX copy_prefix/copy_frame plus JFw_Row.spec and NBR_SemanticStep.source | Ordinary row0..13, valid full buffers, exact source/destination payload arguments after header. Terminates before payload copy; root/header indexed windows use K017/K018. Full native loop association remains OPEN. |
| NBR_scalar (K030) | inherited NBL scalar/circle_sample ports; NBR_OpeningConstruct.source constructs their model traces | Overapproximated arbitrary field value plus state. Checks exact row, nonzero flag, previous/reply state and payload identity. Does not supply scalar-value refinement; no field multiplication is run in Kani. |
| NBR_serialize_cut (K030) | NBR_NativeInactiveSerialize is OPEN | Exact reached inactive argument after gamma. Terminates before serializer result, so no fabricated32-byte result or serializer theorem is claimed. |
| NBR_extend_cut (K030) | KMX append_spec, NBR_VecAppend.extend; one actual iteration K019/K020 plus NBR_AppendInduction and NBR_OpeningPayload | Empty live Vec capacity256, same root32 after kappa/alpha0. Cut terminates. Fission after append uses arbitrary owned initialized Vec256 and retains branch-local drop before query. Result content needs native append induction/source join. |
| NBR_queries (K030) | inherited NBL_QueryTrace / closed-conditional caller composition | Same final_message2048, row31 and alpha1 successor state; arbitrary rejection exercises unchanged scratch and exact destruction position. Not a whole query-loop or success proof. |

Every NBR replacement returning a child Result is a local overapproximation, not a new admitted Lean axiom. Conditional/native pairing gaps are listed explicitly in NBR_prepare_BRIDGE.md. The full native caller must establish all domains and pairings before any composite CLOSED claim.
