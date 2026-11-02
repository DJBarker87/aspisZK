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
