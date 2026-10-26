# Continuation axioms audit

J21999 compiled the final seed-prefix bridge and printed the following 121 distinct theorem results across 59 modules. Only standard axioms occur. The transport print is repeated in raw output. Cached focused dependency closure, not a frozen release replay. See [receipt](J21999/receipt.json) and [manifest](FINAL-AUDIT-MANIFEST.json).

| Declaration | Axioms |
|---|---|
| `R1Z.PV_L2_BoolTrace.value` | `propext` |
| `R1Z.PV_L2_BoolTrace.false_prefix` | `[]` |
| `R1Z.PV_L2_F3AttemptSource.source_projection` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3AttemptSource.owned_projection` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3AttemptSource.complete_l1` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3FullRetry.full_l1_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3FullRetry.rejected_prefix` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3FullRetry.stopping_prefix` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3FullRetry.rejected_rom_prefix` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3FullRetry.l1_events` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3FullSource.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3FullSource.arrays_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3FullSource.pair_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3FullSource.observed_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3PrefixBounds.read_bound` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3PrefixBounds.actual_answers` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3PrefixBounds.request_bound` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3PrefixBounds.failed_read` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3PrefixBounds.diverging_read` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3PrefixBounds.exhausted` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SeedFrames.finish` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SeedFrames.blockHash_seed` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SeedFrames.next_reseed` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SeedFrames.actual_answer` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SeedFrames.refill_frame` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SeedPrefix.transport` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5DivPass.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5DivPass.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5DivPass.pass_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5DivStep.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5DivStep.source_body` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5DivStep.decrease` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5Mle.suffix_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5Mle.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5SparsePred.one_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5SparsePred.boolean_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5SparseSuffix.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5SparseSum.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5SparseSum.run_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5SparseWeight.factor_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5SparseWeight.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5SparseWidth.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5SparseWidth.source_width` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6BCond.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Callers.piv_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Callers.image_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Callers.product_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Checker.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Echelon.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EchelonRow.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EchelonRowStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EchelonRowStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EchelonRowStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EchelonStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EchelonStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EchelonStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Entries.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EntriesStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EntriesStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6EntriesStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6FlagLoop.erases` | `propext, Quot.sound` |
| `R1Z.PV_L2_F6Half.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Half.source_eq` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Half.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6HalfInputs.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6HalfPQ.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6HalfR0.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6HalfR1.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6HalfR2.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6HalfR3.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6HalfShift.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Identity.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6IdentityRow.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6IdentityRowStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6IdentityRowStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6IdentityRowStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6IdentityStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6IdentityStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6IdentityStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Lifts.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6LiftsStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6LiftsStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6LiftsStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6MM.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Null.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullEntry.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullFinish.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullRow.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullRowStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullRowStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullRowStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6NullWant.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6PermutationLeft.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6PermutationLeftStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6PermutationLeftStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6PermutationLeftStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6PermutationRight.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6PermutationRightStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6PermutationRightStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6PermutationRightStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6QPrime.erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_HeadlineJoint.original_refinement` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_HeadlineJoint.agreement_exact` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_InversionPole.producer` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_InversionPole.consumer` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_InversionQ.branch_nonzero` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_InversionQ.logup_operand` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_InversionQ.logup_all` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_InversionQ.zero_exact` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_Premises.rows_agree` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_Premises.same_coupling` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_PremisesBound.joint_test_bound` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_RecordCompact.bind_eq` | `[]` |
| `R1Z.PV_L2_RecordCompact.bind_value` | `[]` |
| `R1Z.PV_L2_RecordCompact.operation_bind_value` | `[]` |
| `R1Z.PV_L2_RecordCompact.fail_prefix` | `[]` |
| `R1Z.PV_L2_RecordCompact.div_prefix` | `[]` |
| `R1Z.PV_L2_RecordRefinement.bind_erases` | `Quot.sound` |
