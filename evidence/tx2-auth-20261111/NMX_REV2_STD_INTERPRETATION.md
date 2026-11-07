# Revision 2 std interpretation

Target not yet established. This note classifies local semantic steps; it adds no trust row or row-input clause.

The canonical targets are the original `RSL.TX2_233.RowSpec_233`, `RSL.TX2_234.RowSpec_234`, and `RSL.TX2_217.RowSpec_217` from the merged revision2 source. All retain their original domains. The original module owners are rebuilt in `NMX_R2_canonical_objects`; every RSL-dependent NMX source in the active chain has a new `NMX_R2_` module name. Old revision1 support is preserved in its separate retained export.

At frozen owned.rs:21–24, `data` clones a deferred `ProgramError`, and `data_len` clones `Result<usize,ProgramError>`. The actual emitted getters are `AdapterRw.r1_pool_adapter.owned.OwnedAccount.data` / `data_len`; `op35` is the reached ProgramError clone. ProgramError's BorshIoError owns a String. As documented and pinned in RSL_REVISION2.md, only a nonempty String needs a fresh allocation. Under the retained std/allocator item, the local interpretation returns an identical error or aborts at that specific allocation site. The abort has only the reached event prefix. Empty strings and payload-free errors have no abort arm. There is no arbitrary divergence or generic may-abort arm.

`NMX_R2_CloneNative` is a proposed emitted-getter step over this std interpretation. Its Boolean allocator indicator covers both outcomes, without selecting child success or restricting accounts. Until its focused acceptance receipt exists it is WIP, not evidence. The `base : Ops` binder in that local lemma supplies unused slots and cannot survive as a free dictionary in a row root.

`NMX_R2_Semantics` interprets the three data occurrences with `RS.ofCloned`, and the verifier-checkpoint guard with revised `verifierCheckpoint`, which includes `data_len`. These occurrences precede the decoder Box sites and preserve their exact source ordering. The four original Box payload/owner tags remain in the typed source program. Nominal owner tags are not asserted to be native pointers. Under (bl)(3), no post-abort heap or cleanup is part of a stopped observation.

The canonical decoder-library association, full native command interpretation, and canonical-versus-raw217/234 association remain separate obligations. Neither the source interpretation definition nor its canonical refinement is silently identified with the actual emitted execution. No new runtime counterexample or security closure is asserted.
