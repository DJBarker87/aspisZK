# Canonical target reconciliation

RSL_TX2_233 / RSL_TX2_242 / RSL_TX2_241 are the binding targets. Existing NMS draft packets are support and are not asserted equivalent to RSL.

* Draft 242: `Law` requires all emitted fail/div arms to coincide with the ideal source Result and entire raw event trace. It has no independent allocation/runtime stop when the ideal source would continue. RSL instead admits allocation aborts at their actual sites, with the event prefix only. The draft cannot be promoted by renaming its `stopped` constructor.
* Draft 242's owner names/freshness and reconstruction linkage retain more allocation identity than RSL, but that does not compensate for the independent-stop mismatch or supply physical interpretation. RSL retains the four complete Box payloads through reconstruction and excludes private drop/allocator internals under (bl)(3).
* Draft 241 `NMS_241OwnClauses.Domain` demands accounts[6] successful bytes always have length1768, and Root0 on every successful proof/checkpoint getter pair irrespective of proof image length. Canonical 241 requires only snapshot consistency (D1) and Root0 when the original proof image is58295 bytes (D2). These are different domains. The stronger draft is retired as a row-input domain; existing local lemmas are not a parent root.
* `NMS_RSLDomains.entered` targets the exact canonical D1/D2 domain, quantifies over arbitrary V2Lib, obtains checkpoint extent from the actual verifierCheckpoint cut plus D1, and obtains Root0 solely at the SAME admitted original inputs through D2. Local successful cuts are proof-internal obligations of the full fold, never exported as new caller clauses.
* `NMS_RSL242Fold.fold` is canonical relational child-call composition with full233 RowSpec at the SAME arguments. Until the actual emitted parent is interpreted in that relation with all CLOSED child/carrier links, it is source support, not a candidate or a ready-for-instantiation native row fold.

G1b: all future241 parent roots quantify over V2Lib and a SAME-call064 refinement on Dom064 V. No global Root0 premise; the True/weaken instance then follows by specializing the proved parametric root. We have not claimed that specialization before the parent proof exists.

## Getter stop difference isolated (L081)
`NMS_GetterStopDifference.clone_stop` proves that a stopped actual op35 clone at the SAME stored error propagates through fresh E003 OwnedAccount::data with no returned reply. `canonical_no_abort` proves RSL's `RS.ofExcept a.data` admits no abort. `not_simulated` proves those getter interpretations are incompatible whenever that clone stops. This is a conditional exact source-interface difference, not an asserted deployed failing execution: op35's concrete stopped/error-clone interpretation must be installed or the RSL getter model must explicitly account for an applicable allocation stop. In particular, no blanket clone-totality/allocation-success premise has been added. A native Rust String-clone allocation counterexample has NOT been constructed. Snapshot callers produce only the two snapshot errors, but canonical 242 has True input domain and canonical241 D1/D2 do not impose that error restriction. No extra snapshot-error restriction has been silently inserted into a row root. Independent canonical-source folds remain valid as stated; native interpretation of the getter is an explicit pending clause.

## Preferred explicit difference: general-error clone stops

NMS_CloneRef234/233/242/241 preserve the original canonical domains, every
returned error/value, the complete Box payloads, and all source effects.
They replace pure stored-error getters with the explicit derived-error clone
interpretation, recursively at the same getter sites. Nonempty BorshIoError
String clone has a private allocation stop; no added unconditional Root0,
no successful-allocation premise, and no snapshot-only input restriction.
NMS_CLONE_REFERENCE_DIFF.json records the textual replacement recipe.
This is a proposed exact difference, not an adopted trust/specification change
and not a concrete deployed-OOM counterexample. The earlier Safe variant is
a separate restricted-domain alternative and earns no canonical row credit.
