# FJu deployed configuration recount

Evidence only. No adoption or authoritative ledger edit. **Target not yet established.**

## Complete statements and mechanical check

Before: `AspisR1.FJu_Top.deployed`, complete kernel type in
`IDb_FJu_Top.BEFORE.lean.txt`. After:
`AspisR1.IDb_Deployed.FJu_Deployed`, complete kernel type in
`IDb_FJu_Deployed.AFTER.lean.txt`. Both freshly printed with pp.all in
passing IDb_007; no elisions in either type.

`IDb_recount.py` checks equality of the entire whitespace-normalised kernel
types after exactly this substitution (IDb_STATEMENT-CHECK.json):

```
(c : DrvC_Installation.Configuration FIo_Install.W CoreError)
  becomes
(adapter : AdapterRw.Ops) (currentBase : AspisR1CurrentCaller.Ops)
(stageBase : VTop_Stages.Ops) (reserved : Bool)

c := deployedConfigurationFull adapter currentBase stageBase reserved
       indexError reservation
```

All other binders and the complete conclusion remain under that substitution.
`FJu_Deployed` is proved by a single application of the existing FJu theorem.
The free Configuration binder disappears; the IDa family loses query and
geometry as implementation-data inputs. No correctness premise is removed.
The native functions, SAME accepted wrappers, arbitrary adaptive adversary,
physical/literal carriers, game, runtime trust, failure events, query budget
(including duplicates/rejected prefixes), and probability/work constants
retain exactly their types and quantifiers. The induced runtime now receives
the selected configuration; equality to every arbitrary old runtime is not
asserted.

## Ledger method

Baseline: evidence/finish-chain1-20261027/FJu_recount.json, pinned in
IDb_BASELINE.json. Preserve all rows, scopes, status, guards and SAME witnesses.
Count conjunction leaves as atomic families; do not multiply a Fin22 family;
keep native/global finish laws distinct; exclude deployment aliases from
distinct totals. Previously removed rows remain removed without new credit.
Returned facts and implementation data are not antecedent law families.

| Basis | FJu_Top before T/P/G/C | FJu_Deployed after T/P/G/C | Delta |
|---|---|---|---|
| Actual antecedent | 83/5/13/0 | 83/5/13/0 | 0/0/0/0 |
| Deployment only | 6/17/0/0 | 6/17/0/0 | 0/0/0/0 |
| Deployment-inclusive non-alias | 89/22/13/0 | 89/22/13/0 | 0/0/0/0 |

Removed=[], added=[], reclassified=[]. IDb_RECOUNT.json preserves the full
row inventory, rather than dropping external deployment tasks because the
kernel statement uses fewer implementation-data binders. The inherited FJu
packet explicitly reconciles its mechanical 17 deployment-only P rows with an
older prose count discrepancy; this recount preserves that mechanical method.

## Actual P rows, retained separately

| Row | Status in both theorems | Exact blocker |
|---|---|---|
| L142 native Pair | Retained P | Seven tensor part meanings and final-message canonicality/operand association on the SAME installed FIn/FIo constructor and native parsed operands. |
| F3Y_G_L142 global Pair | Retained P | SAME source Evidence/Calls/Primitives/literal-view transport for that Pair law. Selection of the source dictionary alone proves no Pair value theorem. |
| L146 native terminal | Retained P | Installed FIq terminal composition VALUE and transport to SAME public/Y/challenges, canonicality and mask/extra operands. Identity of the terminal callback alone is insufficient. |
| F3Y_G_L146 global terminal | Retained P | The corresponding universal accepted source-run/literal endpoint transport remains in FJu_GlobalOwners. Reserved for finish-install20; no borrowed future credit. |
| L154 query budget | Retained P | Original universal issued-query bound on the SAME induced arbitrary adversary. It is a budget condition, unchanged by code selection. |

L143/global matching and L144/L145 native/global are already removed in FJu;
zero additional credit here. The 17 deployment-only P obligations, including
D188-P2 and source-to-ELF association, remain independently listed in JSON.
No ELF/source adoption, allocator/runtime certification or new trust item.

## Non-vacuity

`IDb_Nonvacuity.conditional` applies the original admitted-runtime
non-vacuity theorem at THIS configuration. It preserves the SAME complete
real-byte accepted native pair, supported-entry witness, H-consistency and
actual fixture bytes under the original premises; it does not manufacture
acceptance. `owners_equivalent` specializes FJu's old/reduced owner equivalence
at the same configuration. Both checked in006, re-audited007, standard axioms.

This is conditional preservation, not a constructed joint release witness.
No success law or false Prop is stored in the configuration: it contains
operations and data only. Both allocation outcomes remain exposed. Complete
joint inhabitation of native/extraction/runtime/game/owner premises is still
open, and is not inferred from separate fixture or component successes.
