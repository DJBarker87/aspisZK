# Stage C: focused rebuild; complete replay pending

The three stale proved modules all compile **without source edits** against
the headline cohort. No theorem failure against the current AdapterRwModel
was observed. In particular JGx_SdkAfterValidationEq.source compiles against
Adapter object 010bcafd… . The recovered stage2_owned source diff is empty;
the whole Adapter source diff is limited to a trailing #print command.

| Attempt | Module | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| NER_R020 | JFw_Validator | 0 | 1.284517 | 2640976 | 0 |
| NER_R021 | JGx_SdkAfterValidationEq | 0 | 2.038789 | 4398940 | 0 |
| NER_R022 | JFw_Chunks | 0 | 1.933081 | 4297564 | 0 |
| NER_R023 | JFw_BlockValidation | 0 | 1.996257 | 4295208 | 0 |
| NER_R024 | JFw_Record | 0 | 2.530795 | 4318944 | 0 |

Each source is byte-identical to its repository input. The dependency order
is respected: Validator precedes Chunks, which precedes Record; the SDK
module has no stale ancestor and was independent. BlockValidation also uses
the rebuilt Chunks. The own-cache overlay precedes the read-only NDR cohort;
runner receipts pin each actual selected direct object. Original objects
were neither overwritten nor removed. The five output hashes and source
hashes are in NER_REBUILT_OBJECT_PINS.json. Every theorem printed only
propext, Classical.choice and Quot.sound. Source revision for these attempts
is 948420a8b2 (full hash and exact commands in each receipt).

NER_R025 compiles the unchanged hardened NEP walker as NER_Walker.lean
(byte-identical to evidence/axaudit2-20261102/NEP_WALKER.lean). The standalone
focused driver uses explicit private importAll loading and initialized
extensions, then the exact NEP.audit implementation.

| Attempt/root | Raw constants | Edges | Complete | Equal collectAxioms |
|---|---:|---:|---|---|
| R026 / JGx_SdkAfterValidationEq.source | 3529 | 50951 | yes | yes |
| R027 / JFw_Validator.loop_valid | 2914 | 41484 | yes | yes |
| R028 / JFw_Record.success | 4266 | 63001 | yes | yes |

All three raw axiom sets are exactly Classical.choice, Quot.sound, propext.
The exact #print lines, wall time, peak RSS, zero swaps, source revision,
source hashes, dependency fingerprints and caps are in R026-R028 receipts
and NER_ATTEMPTS.jsonl. Reachable-name lists and NER_AXIOMS.json are retained.
These are focused results; they do not certify the combined release closure.

## Outstanding replay

The module import graph requires **1,387** modules to be rebuilt after the
three stale objects. Five have been rebuilt; **1,382 remain**. The original
budget is 200 focused module scopes. At one module per attempt, that budget
cannot cover this graph even before scanner/audit helper scopes. The fully
ordered plan, all 1,387 unchanged repository source hashes and old object
hashes are in NER_REBUILD_PLAN.json. All sources were located; none needs
editing to make the observed frontier compile.

A budget expansion to 1,450 focused scopes was requested. No expansion had
been received when this handoff was prepared. No full replay was launched
with an impossible remaining budget. This is a budget constraint, not a
reported theorem failure. No source repair was substituted for the requested
rebuild. The current mixed overlay is not claimed to be a coherent rebuild.

Both agg16 allowances remain unused. Do not use them to re-audit the mixed
overlay as though the 1,382 outstanding rebuilds had happened. After the
complete dependency-order source rebuild, run the final aggregation and
hardened private walker on both specified roots, plus NER.loadedScan. Both
walks must complete, equal collectAxioms, and the final loaded scan must
have zero dangling references. That gate has **not run**.

## Authorized continuation, 2026-11-02

Lead superseded the one-module-per-scope limit for this continuation: up to
120 batch scopes, each MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0,
TasksMax 64, -M7000 and at most two concurrent Lean processes. This driver
uses one sequential Lean process in one admitted scope at a time. The two
agg16 allowances remain reserved for final whole-closure aggregation/audit.
Batches contain at most 40 modules in the pinned dependency order. Existing
proved sources are copied byte-for-byte and hash-checked before compilation.
The unchanged lead S2W_run_host runner records each batch's limits, process
peak RSS, swap, exit and wall time. The payload records per-module commands,
source/object hashes, selected import object hashes, time, RSS, swap and any
#print axioms output. The final loaded scan runs in the aggregation environment.


After B005, the local serial submission controller was paused while its
already-submitted B006 scope completed normally. The continuation uses
NER_parallel_batches.py: at most two independently admitted scopes, one Lean
process per scope. Its ready-set rule excludes in-flight imports; every
required direct import must have completed successfully or occur earlier in
the same batch. The pinned dependency graph and source bytes are unchanged.
No submitted compilation is cancelled or resubmitted for this scheduling change.


Preflight for the aggregation boundary: the original NDR_A001 receipt uses
-M15000 for NDR_CombinedAudit. The batch controller was paused after B013;
B011 and B013 both completed and their receipts were recovered without
resubmission. NDR_CombinedAudit is excluded from 8 GiB scheduling and will
compile unchanged inside the one final agg16 scope before the audit driver.
NER_R029 tests the exact new final scanner definitions on a deliberately
malformed recursor rule and a body-removal control: exit 0, 3.314852 s,
2,338,728 KiB peak RSS, zero swaps. It detects exactly NER_RecursorMissing.
This adds recursor rules and declaration name metadata to type/value and
constructor-reference coverage. The unchanged NEP hardened raw walker is
retained separately. No new logical theorem is introduced by this control;
#print axioms is N/A for the inspection program.


## Pre-aggregation checkpoint, 2026-11-03

All 1,386 ordinary targets pass in 37 batches (34 batches of 40, then
6, 14 and 1 modules). The only pending source compilation is NDR_CombinedAudit,
reserved for agg16. NER_rebuild_checks.py --partial validates every selected
affected import against its rebuilt output and rejects a planted stale hash.
The shared quiet window caused five refused admissions (exit 78); the barrier
then admitted both waiting batches before the stated window end. No marker
was changed and no refused scope was launched.

NER_R030 compile-only checks the actual standalone final driver: exit 0,
0.727410 s, 1,586,408 KiB peak RSS, zero swaps; an unused-argument warning only.
No target closure is loaded by this syntax check. R029/R030 are conservatively
charged as two additional capped control scopes. No new logical theorem is
introduced by either program, so #print axioms is N/A for these controls.

NER_preaggregate.py verifies all original object/private pins, every rebuilt
output and 34,042 selected/retained kernel or IR files. It also checks the
Lean binary and hardened walker against their prior recorded hashes.
NER_PREAGG_OBJECTS.jsonl is input to the final scope; its selected files are
checked before compilation and again after the audit. The original cohort is
retained read-only. No final coherent/raw-root claim is made at this checkpoint.


## A900 scanner representation failure and correction

NER_A900 compiled the unchanged NDR_CombinedAudit successfully in 6.376899 s.
The combined scope exited 3 after 85.086928 s, peak RSS 12,214,488 KiB,
swaps 0. It verified every pinned input before/after. No raw root walk began.
Its loaded scan found zero missing references across all 16,058 modules,
1,520,745 active declarations and 38,049,122 reference occurrences.

The checker compared duplicate-bearing merged loader imports to the original
manifest's stable-unique projection. Exactly 13,935 lists failed that raw
comparison; stable first-occurrence projection matches all 16,058 exactly,
including order. NER_ModuleTables.inspect already defines that projection by
de-duplicating across public/server/private parts. This is an own checker
error, not a theorem failure or discovered import drift. The loaded declaration
count equals the original serialized unique-name count module by module;
2,316,265 serialized entries include duplicates, rather than missing bodies.
NER_A900_DIAGNOSIS.json and NER_LOADED_A900.jsonl preserve the failure.

NER_FinalDriverV2 uses that same stable projection, preserves raw loader lists,
and reads each own declaration from the checked private kernel map before
following its types, values, recursor rules and name metadata. It attempts both
raw walks even after a scan failure, while final exit remains nonzero on any
failure. R031 passes dangling/body-removal and stable-projection controls,
rejecting missing, extra and reordered import mutations (3.600806 s,
2,340,476 KiB RSS, swaps 0). R032 compile-only checks V2 (0.760297 s,
1,584,952 KiB RSS, swaps 0). All 1,387 rebuilt outputs and import hashes pass.

A901 is the remaining, changed-shape audit allowance. It reuses the successful
A900 model object, with no unchanged model recompilation. Its 34,043 pinned
files include that new object and the retained original read-only cohort.
Both raw roots and the corrected loaded scan must still pass before success.
