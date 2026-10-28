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
