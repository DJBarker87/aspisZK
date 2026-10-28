# NCP substitution ledger

No field-multiplication or digest/syscall stubs are used; no LPh arithmetic stub obligation is added. K-2 quarantined harnesses: none. Word K024-K027 is diagnostic only and not a claimed codec leaf.

## Prescribed copy replacements

The exact KMX patch is bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No copy stub was written here.

| Reached form | Replacement | Existing Lean value law / domain |
|---|---|---|
| copy_from_slice, clone_from_slice | KMX_copy_from_slice, KMX_clone_from_slice | KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame; typed Copy elements, equal lengths, valid slices |
| ptr::copy_nonoverlapping | KMX_copy_nonoverlapping | same loop/frame laws; valid disjoint typed Copy regions, established by the safe std conversion/copy caller |
| Vec extend_from_slice, to_vec | KMX_extend_from_slice, KMX_to_vec | KMX_CopyMeaning.append_spec; safe Copy elements and successful allocator semantics |
| realloc | KMX_realloc | KMX_CopyMeaning.realloc_prefix; valid old layout/allocation, successful-reallocation byte prefix and preserved old allocation on failure |

The Vec controls do NOT admit Vec verified substitution (Arbitrary codegen failure). Matching failing controls for credited local codec/helper uses are enumerated below, never inferred from the replacement's name.

## Function contracts

| Actual callee | Callee pass / failing control | Caller pass / failing control | Domain and Lean reference equality |
|---|---|---|---|
| atomic_statement::decode_digest_canonical | K038 / K039 | K040 / K041 | all32-byte inputs; NCP_DecodeReference.reference_source |
| pair_tree_profile::digest_is_canonical | K042 / K043 | K044 / K045 | all raw eight-limb digests; NCP_CanonReference.source; NBD_DigestInduction.source supplies decreasing loop induction |
| pair_terminal::exact::<8> | K058 / K059 | K060 / K061 | byte slice length<=33, width8 only; NCP_ExactReference.source; after_index caller range theorem |
| pair_terminal::exact::<32> | K062 / K063 | K064 / K065 | byte slice length<=33, width32 only; same reference equality; after_digest range theorem |
| pair_tree_profile::digest_is_canonical in one frontier step | K042 / K043 | K068 / K069 | arbitrary record/prestate and level<20, exactly the native loop guard; NBH_Frontier.afterstate_loop model induction retained |
| pair_terminal::validate_verified_afterstate | NONE: K066 timeout | NO CREDIT: earlier K056/K057 lack a verified callee | whole method contract OPEN |

Weak contracts and deliberate bad modifies/ensures are fidelity controls only (K001-K023), not additional trusted source substitutions. Digest Result's complete shape controls are K018-K023. Original exact K046-K053 omit an explicit function-contract domain bound and are superseded; no general native exact law is claimed from them. Native error carriers stay typed; no raw-byte output havoc or function-pointer representation is used.
