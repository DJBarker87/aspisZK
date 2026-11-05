# NIQ exact open edges

TX2:129 and TX2:115 remain OPEN. No new trust row, predicate weakening, successful-result assumption or ledger promotion. The new allocation and powers7-prefix cuts remove concrete missing observations from NIQ_CUTS, but they do not establish native semantic composition.

## Pair: Initial/powers4 post → regular/low pre

Native record: NIG_stages.patch `Initial`, `initial_stage`, receipts NIG_K111/112, hashes NIQ_INPUT_PINS. Exact post, for arbitrary side/power/limb in the checked finite ranges:

```
Initial.inputs[side].to_limbs()[limb] = alpha[side].to_limbs()[limb]
ap[side][power].to_limbs()[limb] = Initial.replies[side][power].to_limbs()[limb]
Initial.calls = 2; parts[slot].to_limbs()[limb] = 0
```

Next model cut's pre: the decoded SAME `ap0/ap1` are exactly the arrays returned by `FIo_Native.weights.powers 4#usize` on the decoded SAME alpha. `NIG_PairValues.powers4` proves canonicality of those emitted outputs; `NFW_PowersCohort.source` supplies the callee equation. Neither proposition mentions Initial/replies or provides its encoding into those arrays. The native record allows any canonical replies. There is no imported NIG local-record proposition connecting those reply fields to the callee instance. That association is the missing edge, not a need to re-prove powers or a failed numerical multiplication.

The same precise distinction recurs at **Common→shared_partials**, **Low→grouped_inactive_pair**, **LibraLog→next Libra iteration**, and **Final→next final iteration/return**. Native post is a selected-cell/limb update in terms of logged opaque replies; the next emitted invariant is on the SAME full Array/State with those replies interpreted by the callee packet. NIG's frame/induction laws are on the emitted variables, not a relation to the native local-record fields. NIQ_RawWindows/FieldDomains now prove byte selection, size, canonicality and SAME proof-backed source indices; they do not invent that missing native record carrier.

The exact additional deliverable is a typed interpretation of the existing native records, with its cut-local certificate propositions, on which the imported NIG frame/step equalities can act. **Classification: missing formal record/encoding association.** No tool limit or shipped semantic mismatch is asserted. The instruction requires existing NIG statements to be imported, not restated; this job does not replace absent imported propositions with newly chosen definitions or an endpoint equality hypothesis. NIQ_INTERFACE_INVENTORY.json records the inspected exports, not a claim that a mathematically suitable interpretation is impossible.

## Finish: PairPort post → NHT afterWeights / FinishLog post → full Result

Native records: NIG `PairPort`117/118 and `FinishLog`119/120. PairPort post forwards `encoded(out)=encoded(reply)` with SAME owner/alpha/f/kappa; its `reply` is an arbitrary canonical Ok or any of the eight verifier Err variants. Next NHT pre is `PairLaw installed v p weights alpha (NIG_PairExport.packet r weights alpha v.final_message p.kappa)`. This is an exact op2 equation on that model instance. NIG_PairExport.NHM_pair establishes that model equation; it does not interpret PairPort.reply as its value. Pair's open edge must supply this association; it cannot be assumed by finish.

Independently, FinishLog post gives source-ordered events, selected arguments, full Rust returned Error/unit, first-error/no-suffix and Relation/Query outcomes for arbitrary replies. The NHT packet consumes outer Aeneas `Result (core.result.Result Unit Error)`, including fail/div abort prefixes and exact callee results. **NIQ_ResultEncoding proves an injective eight-error projection preserving fail/div**, and NIQ_FinishComposition retains the exact model equation and first-round rejection/fail/div prefixes with primitive Domain. What is still absent is the cut-local typed interpretation from FinishLog and child observations to that encoded model execution. An injective encoding cannot manufacture an equality between unassociated values.

**Classification: missing formal record/encoding association plus OPEN pair ancestor.** No new Kani window is justified merely to reproduce119/120. No whole-function output-equality premise is added. RuntimeSyscall, allocator and (an) abort-prefix trust remain as inherited; NIN-R2 and RuntimeCpiReadonlyEntry7 stay PENDING and unused.

## Retained caller boundary

NHV/NID supplies `NIG_FinishInput.Domain proof v p a` at the actual finish call. It is explicitly retained in every finish theorem. Neither caller-domain closure nor producer success is claimed here. The exact allocation failure and returning ownership match, and powers7/zero-sum prefix, now have NIQ native observation/control pairs; they earn local cut credit only (NIQ_CERTIFICATES).
