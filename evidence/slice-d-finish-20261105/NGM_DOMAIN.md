# TX2 finish caller domain

The boundary is candidate.rs::tx2_common at the final call to finish_relation, after the successful query_loop and BatchedWeights::finish. tx2_common and tx2_authenticated remain NFW-owned. No successful finish, correct claim, pair equality, dot equality or accepted spend is an incoming premise.

## Established accumulator predicate

`AspisR1.NGM_FinishDomain.AccumulatorDomain a` states exactly:

- `a.weights.val.length = 64`;
- every SAME returned weight satisfies `Port3_FlushInstall.Canonical`;
- `NBO_TailDomain.WideCanonical a.rhs`;
- `NBF_PowerStep.Canonical a.power`;
- `a.next.val = 22`.

`tx2_writeback` derives this predicate from the SAME successful TX2 query_loop result, the NFS invariant `Domain p 10 22 a pending`, and input next=10. It existentially returns the exact flush output, proves flush returns it, reconstructs the accumulator with those bytes/fields, and proves rhs/power/next unchanged. The query result and pending object are not independently selected. The proof imports NGC_QueryPoststate and NGC_FinishFrame from immutable commit recorded in NGM_NGC_PROVENANCE.json, under prefix-owned module filenames; no sibling worktree is read or edited. NGC's total flush law needs no allocation-success or successful-finish premise.

## Remaining Prepared / view producer boundary to NFW

At the SAME finish call, NFW must supply p.variant=S2; canonical p.claim, p.alpha[0], p.alpha[1], p.kappa; canonical ten semantic_alpha coordinates and all four QM31 coordinates of p.z; and the SAME proof-backed relation view:

- round0 = proof[OFF_ROUND0..OFF_FOLDED_ROOT], length224;
- round1 = proof[OFF_ROUND1..OFF_FINAL], length224;
- final_message = proof[OFF_FINAL..OFF_OPENINGS], length2048;
- every one of the seven / seven / sixty-four 32-byte field windows has eight little-endian words <2147483647.

These are data/provenance obligations, not child-result assumptions. No allocation availability is required. Weights::new, Weights::pair and dot may reject with their exact errors; all such errors must remain rejections. Once their selected packets exist, their precise local domains must be checked against this predicate before it is called sufficient. In particular no CLOSED Weights::new/pair packet is currently available in ledger8, so this document does not assert that a complete sufficient packet domain has already been proved.

## Native caller-control domain

The earlier K005..040 control scaffold fixed the accumulator weights at zero and used adjacent round windows; those checks are fragments, not a general caller-domain certificate. K083 replaced it with full canonical arbitrary weights and the exact S2 geometry but timed out. No native credit is assigned to K083.

K084..099 isolate data-independent control from field validity: S2; all64 raw QM31 weights arbitrary; next/rhs/power/inactive and relevant Prepared fields varied; all2528 proof bytes unconstrained; round windows [0..224] and [256..480], final [480..2528]. The stronger raw message/weight domain avoids eagerly evaluating632+256 validity conditions that control does not read. Results remain pending until their individual receipts are checked. The reference replies still carry arbitrary canonical E values (E::new), every deployed Error, and the full owned Weights record. No successful child is assumed. The deployed observer is literal None. Field-callee validity and producer obligations remain separate and OPEN; a passing control fragment does not discharge them.

## Acceptance condition, without dropping errors

finish_relation first requires round0 Ok; on the two-fold branch round1 Ok; then new weights Ok and pair Ok; pair must equal the last round claim. It marks Relation, requires dot Ok, and requires next=22 and actual=rhs. It marks Final and returns exactly Ok(()). A child Err is returned unchanged; unequal pair returns Relation; non-22 next or unequal actual returns Query. A model runtime failure/divergence is preserved by the full extracted Result carrier. NGM_FinishControl.source is exact source-body equality with these callbacks, not their implementation discharge.
