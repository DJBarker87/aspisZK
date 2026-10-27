# ARX deployed-configuration recount

Evidence only. No adoption, authoritative ledger edit, contract edit or ARX_Root edit. **Target not yet established.**

## Complete before/after statements

- Before: `AspisR1.ARX_Root.deployed`, full kernel type in `IDa_ARX_Root.BEFORE.lean.txt`.
- After: `AspisR1.IDa_Deployed.ARX_Deployed`, full kernel type in `IDa_ARX_Deployed.AFTER.lean.txt`.
- Fresh audit: `IDa_004/stdout.log`, exit0. Both root types use pp.all and have no elisions.
- `IDa_recount.py` checks the complete whitespace-normalised printed type, not a binder-count heuristic: replace the one Configuration binder by `missing : IDa_Deployed.Uninstalled CoreError`, substitute `c := deployedConfiguration missing indexError reservation` everywhere, and rename the theorem. The resulting type equals the entire after type exactly. `IDa_STATEMENT-CHECK.json` pins both types and that check.

Proof: direct application of ARX_Root.deployed; there is no new security proof in the corollary. The root's further FIp selection remains visible. Selected finish/boundaries/std projection facts are separately proved; no unchecked whole-record idempotence assertion is used.

## Ledger method and counts

Reuse Rc12/Rc11 atomic law families: split conjunction leaves, preserve SAME existential witnesses and guards, count Fin22 matching once per family, keep native/global finish rows separate, exclude deployment aliases from distinct totals. Returned facts/data binders are not new hypotheses. `IDa_RECOUNT.json` retains every baseline row with an explicit disposition; `IDa_recount.py` verifies the full inventory/counts. This is a recount of the specialized theorem, not adoption of a revised ledger.

| Basis | ARX_Root before T/P/G/C | ARX_Deployed after T/P/G/C | Delta |
|---|---|---|---|
| Actual antecedent families (including nested native finish implications) | 83/11/13/0 | 83/11/13/0 | 0/0/0/0 |
| Deployment only | 6/17/0/0 | 6/17/0/0 | 0/0/0/0 |
| Deployment-inclusive, excluding aliases | 89/28/13/0 | 89/28/13/0 | 0/0/0/0 |
| Raw including aliases | 89/28/13/0 | 89/28/13/0 | 0/0/0/0 |

Removed=[], added=[], reclassified=[]. In particular, replacing free implementation data by code does not discharge its semantic law. The binding facts below are provable definitions; they were not distinct counted P rows in the starting ledger, so they earn zero removal credit.

## Concrete code facts versus retained premises

| Item | Effect of specialization |
|---|---|
| Configuration data binder | The whole free c disappears; the six explicit residual inputs remain in `Uninstalled`. This is implementation data specialization, not a removed P/T/G law. |
| Terminal callback identity | Now `FIq_Terminal.terminal` by terminal_fixed and selected_fields; no arbitrary terminal callback remains. No equality premise was added. |
| Finish callbacks | All twelve fields are IDa_Deployed.finish reservation by finish_fixed/selected_fields; Pair/newWeights are the FIo/FIn source bodies, release control leaves explicit. |
| Other boundary callbacks | All eight are IDa_Deployed.boundaries reservation by boundaries_fixed/selected_fields. Root-copy and Claims are selected explicitly; mask arithmetic and circle use FIp/Rc5 bodies. |
| Std callbacks | NP6_StdModel.calls reservation by selected_fields. Content/value interpretation only; native std correspondence is not derived. |
| L078/L079/L080 extraction | Still retained T boundaries, now about DrvC_Installation.sdk of this partial source installation. Stage1, stage2 and digestSource equivalences are not proved by choosing the record. |
| L001–L077 SDK/std/runtime admissions | Unchanged; no library, allocator or runtime proof follows from selecting verifier leaves. |
| L081 P1 / L082 syscall | Unchanged. No new oracle or native digest realization is derived. |
| L083/L084 accepted wrappers | Same native1/native2, verifier, bytes, heaps and output witnesses. Acceptance is neither manufactured nor removed. |
| L154 query budget | Identical universal bound on ARW_Induced.issued for the same arbitrary adversary, native1, copy and allocator; duplicate/rejected-prefix charging unchanged. |
| RuntimePersistence / game fields | Same 1T and 11G families, plus the other inherited G families. No runtime/history property discharged. |
| Deployment-only obligations | All retained: artifact/model association, whole-source correspondence, trust-inventory and library/runtime gates still need their existing certificates. No re-credit for earlier ELF reproduction or cohort replay. |

A local arithmetic/identity theorem can now be stated about the chosen body. It is not automatically a proof of the SAME native/literal/physical argument association demanded by the root. In particular “concrete installed code” does not imply that all its semantic properties are already proved.

## L142–L146: exact retained families

All ten rows below remain P, independently counted.

| ID | What is fixed | Exact remaining blocker |
|---|---|---|
| L142 (native) | FIn constructor / FIo Pair body in the native finish implication | Seven tensor-part meanings on the SAME prepared inputs, final-message parsing/canonicality and both model dual folds; full native/model operand association. |
| F3Y_G_L142 (global) | Same Pair/newWeights bodies in FIp_GlobalOwners | The above value law on the SAME source Evidence/Calls/Primitives, prepared literal view and physical data; owner premise retained. |
| L143 (native) | Matching still ranges over the SAME 22 selected queries | fast_dots values on the SAME width29 powers and opening bytes, per-index value and 22-index join; fixing query.op20 alone does not prove matching. |
| F3Y_G_L143 (global) | FIp_DotsAdapter.dots source chosen | SAME source data/powers/opening transport for every query; owner premise retained. |
| L144 (native) | Concrete semantic preparation/boundaries | Initial native EquationEndpoint polynomial/claim association on the SAME returned native witnesses. |
| F3Y_G_L144 (global) | Concrete semantic preparation/boundaries | Owner initial-equation leaf remains in this direct ARX corollary. FIr_PhysicalInitial.on_run is useful prior work on the separate FIr/FIq path; it is not applied to remove an ARX binder here. |
| L145 (native) | Concrete semantic preparation/boundaries | All nine SAME native polynomial/challenge adjacency equations. |
| F3Y_G_L145 (global) | Concrete semantic preparation/boundaries | Owner chain-equation leaf remains. FIr_PhysicalChain.on_run/GlobalOwners2 are not silently substituted for FIp_GlobalOwners in this corollary. |
| L146 (native) | FIq_Terminal.terminal is now the actual chosen callback | Complete masked composition VALUE on the actual returned typed view, canonicality and transport to the SAME public/Y/challenges. Code identity removes the arbitrary-callback obstruction, not this semantic obligation. |
| F3Y_G_L146 (global) | Same fixed FIq terminal, source owner | The SAME source accepted-run VALUE plus physical/literal public/Y/challenges/coordinate/mask/extra transport. No source-global owner leaf is discharged here. |

FJn_InstallationSeparation.not_uniform remains valid for arbitrary c. It does not obstruct this particular selection, nor establish the selected terminal value law. FIr's historical removal of its global L144/L145 is not new removal from the adopted ARX corollary; the starting ARX ledger retains both, as does this theorem.

## Non-vacuity

`IDa_Nonvacuity.conditional` applies ARX_Nonvacuity.conditional at this exact selected c, preserving the SAME real-byte native pair, H-consistency, SupportedEntry and returned accepted run. It adds no correctness/acceptance premise and does not weaken those prerequisites. The constructor carries only operations/data, no proof field hiding acceptance or the conclusion. Both reservation outcomes and arbitrary residual records remain quantified.

This is conditional non-vacuity preservation, **not** a constructed joint release inhabitant. Existence of the complete accepted extracted native pair and retained runtime/game tuple is still open. Separate terminal/Pair fixture successes are not promoted to that joint witness.
