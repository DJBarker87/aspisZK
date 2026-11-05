# NHA toolchain-change assessment

**No Aeneas patch is proposed or adopted.** There is no demonstrated minimal local fix that makes all three shapes extract, so no NHA_aeneas_<hash>.patch or successful regression result is asserted. No patched executable is used in any attempt.

## Exact pinned implementation

The receipts pin Aeneas b59d5188-lean432-extended, executable c0cf4fcc..., recovered historical source tree3be6820e84debbb8f2cc6b61abca478e98157bc7. The private source matches all38 historical changed-file hashes (NHA_TOOL_SOURCE_PROVENANCE.json). This is different from d860ac47. Charon reports0.1.223 and embedded toolchain nightly-2026-06-01; prior recipes set RUSTUP_TOOLCHAIN=nightly-2026-09-17, which is recorded separately, not mistaken for its compiled version. All Charon runs use the pinned executable, default sysroot and original --mir built preset.

## Failure sites and why a one-line workaround is insufficient

InterpReduceCollapse.ml:1991 applies total Map.find to every abstraction named in shared_borrows_seq after replaying a merge sequence. The map is populated for actual merges or one-sided surviving abstractions. Both missing means no mapping. A fallback to the old identifier would only be justified when that abstraction still exists in the projected context with the required borrow slot, type, region and marker. If it does not exist, silently skipping the shared borrow loses semantic information. Neither condition is established by the exception alone. The ordinary get_id helper earlier in this function is not proof that using it at this different stage preserves those obligations.

InterpBorrows.ml:2731 requires PNone for ASharedLoan while ending unused shared loans during dummy-value simplification. Its callers can be reached during collapse with a marker-bearing loan inside an ignored mutable borrow. Removing this check, forcing PNone or blindly discarding the abstraction would change the borrow semantics being translated. A correct repair must establish when/how projection markers are erased before this simplifier and preserve the continuation, not merely allow emission.

The two sites have different preconditions. A single swallowed exception or weakened invariant is not a minimal sound fix. The field outlining test retains the assertion inside its isolated helper, narrowing the issue beyond just syntactic nesting.

## d860ac47 precedent

The host patch is copied read-only under NHA_source_inspection/NHA_PRECEDENT_aeneas-d860ac47-preserve-distinct-loop-input-abstractions.patch. It filters direct fixed-input/fixed-input merge pairs when projecting a join, preserving independent recursive backward interfaces. It changes neither the total mapping operation nor the loan-marker invariant directly. Its comments rely on collapse treating later absent synthetic merge outputs as no-ops. Porting this to a different extended source without a regression/fidelity argument would add tool trust.

The requested `git grep d860ac47` admission entry was not found in this branch's docs/.../design tree. The found C3-BIN entry at lines3619ff adopts the XRa b59 extended functional pin; it is not an admission of the d860 patch for this pin. The older precedent is therefore inspected, not treated as automatically admitted. Applicability dry-run receipt: NHA_PRECEDENT_CHECK.json. The hunk DOES apply cleanly at line1805 (offset242); patch --dry-run exits0. It was not applied, built, or extraction-tested. Textual applicability does not establish that it fixes these shapes or preserves emitted semantics.

## Adoption gate for a successor

A justified patch must first make all three exact LLBC shapes succeed within the unchanged caps and timeout policy. Re-emit at least ten prior frozen functions using identical namespace/options and compare full Lean bytes and hashes before/after, preserving all failures. Record the patch line by line and input/source/tool/build hashes. Any proposal is **ADDED-PENDING-LEAD under narrowed D188**; only the lead can adopt it. This job does not add such a trust item as an accepted premise or use patched emissions for credit.
