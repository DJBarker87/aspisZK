"""Build the exact declaration and import inventory from J26201 receipts."""
from pathlib import Path
from collections import Counter
import json,re
r=Path(__file__).resolve().parents[2]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/formatter262'
x=json.loads((e/'26201/receipt.json').read_text());c=json.loads((e/'closure-input.json').read_text());im=json.loads((e/'formatter-importers.json').read_text())
log=(e/'26201/out-26201.log').read_text();owners=dict((n,m) for m,n in re.findall(r'^OWNER\|([^|\n]+)\|([^\n]+)',log,re.M))
allowed={'propext','Classical.choice','Quot.sound'}
rows=[dict(module=owners.get(v['name']),**v) for v in x['print_axioms']]
bad=[v for v in rows if set(v['axioms'])-allowed and v['name']!='Aeneas.Std.core.fmt.Formatter']
assert x['exit_status']==0 and not x['errors'] and not bad
by=Counter(v['module'] for v in rows if v['module'])
(e/'declarations.json').write_text(json.dumps(dict(axiom=im['axiom'],nonstandard_candidate_dependencies=bad,declarations=rows,module_counts=dict(sorted(by.items()))),indent=2)+'\n')
lines=['# Formatter dependency closure — Stage 0','','Candidate revision `af96787aa3`; branch `codex/cx-prover-dict-20261026`.',
'', '**Result:** no audited candidate declaration depends on `Aeneas.Std.core.fmt.Formatter`. This is an axiom-dependency result, not native Formatter adequacy or a deployed privacy conclusion.',
'', '## Exact scope', '',c['qualification'], '',f"Audited {len(c['audited_modules'])} selected family modules in {len(c['modules'])} source modules. Every declaration owned by a reachable `PDict_`, `ProverRw*`, `PV_CB_*`, or `PV_CB3_*` module was passed to the actual `#print axioms` elaborator, including private/generated declarations. All 28 `ExternalTypes.op0`–`op27` projections were also printed. Definitions of the installed representations and their installation theorems are included, including the conditional Error3/Formatter27 reference carriers.",
'', '`ProverRwFull.ExternalFuns` and `R1Z.ProverRwP6BodyData.refinement_of_data` were printed explicitly. The eight import roots and every source/object hash are in `closure-input.json` and `26201/26201-input.json`. Some modules contain audit commands only and own zero declarations. This is a focused cached audit, not a coherent frozen release rebuild.',
'', '## Axiom identity and import inventory', '', '`Aeneas.Std.core.fmt.Formatter : Type` is declared by `Aeneas.Std.Core.Fmt` (retained exact source: `Fmt.lean.txt`). Its diagnostic `#print axioms` correctly reports `[Aeneas.Std.core.fmt.Formatter]`. It is distinct from the candidate alias `ProverRwFull.core.fmt.Formatter`, which is external type slot 27.',
'', f"{len(im['import_paths'])} project modules transitively import the backend module. Every importing module and a complete witness import path is in `formatter-importers.json` and the appendix below. Importing that module does not make a declaration depend on its axiom. **Candidate declarations with this axiom: none. Candidate modules owning such declarations: none.**",
'', '## Before/after axiom table', '', '| Target | Before (J26201) | After Stage 0 |', '|---|---|---|',
'| Backend diagnostic `Aeneas.Std.core.fmt.Formatter` | forbidden axiom itself | unchanged; unselected |',
f"| {len(rows)-1} candidate/root/type-slot reports | subset of `propext`, `Classical.choice`, `Quot.sound` | unchanged; no dependency to eliminate |",
'| `ProverRwFull.ExternalFuns` | `propext, Classical.choice, Quot.sound` | unchanged |',
'| `ProverRwP6BodyData.refinement_of_data` | standard subset (full exact list in receipt) | unchanged |',
'', '## Ledger disposition', '', '**V269 and V270: CLOSED-ON-CANDIDATE for the lead-requested Formatter RELEASE BLOCKER only.** Exact statement: “At the pinned candidate sources/objects inventoried here, every audited candidate declaration, all 28 external type-slot projections, ExternalFuns and the P6 refinement root have axiom closure contained in `{propext, Classical.choice, Quot.sound}`; none uses `Aeneas.Std.core.fmt.Formatter`.”',
'', 'Before: both OPEN under recount 2; D203 did not justify native type27 reduction. After: the requested standard-axiom closure condition is checked on the candidate without replacing a type or proof. No quantifier, carrier, simulator, observer, hypothesis, conclusion, shipped source or backend changed. **The broader native type27 sink/value/options/failure/state association remains unproved and is not credited as removed. Native type count remains 26/28; source selection remains 175/255.** This scoped status must not be read as native adequacy or closure of V038.',
'', '## Route and existing symbolic obligations', '', 'Stage 0 clean-closure branch. No Stage 1 modification is necessary for the mechanical axiom target. The preferred avoidance route already exists in the pinned candidate: `PDict_FmtPublicationFrame.publication_frame` (namespace `R1Z.PDict_FmtErase`) factors publication before `erase_420`; `PDict_FmtRetryComplete.erase_425` uses `fixed_equal`. Those files exist on the candidate branch but are not imported by the selected dictionary closure; no audit credit is claimed for those unimported files. The stale failed `PDict_FmtErase26` source is not imported; its split successors are. No large-term reduction was attempted.',
'', '## Receipts and budget', '', '| Attempt / target | Exit | Wall | Peak RSS KiB | Swaps | Revision | Axioms |', '|---|---:|---|---:|---:|---|---|',
'| J26200 `R1Z/PDict_FormatterClosure262` | 130 | 2:02.20 | 4359800 | 0 | af96787aa3 | no completed output; manually interrupted to replace repeated environment scans with one scan |',
f"| J26201 `R1Z/PDict_FormatterClosure262` | {x['exit_status']} | {x['wall']} | {x['peak_rss_kib']} | {x['swaps']} | af96787aa3 | {len(rows)-1} standard-only candidate reports; one deliberate backend diagnostic |",
'', 'J26200 is charged. J26201 changed the audit algorithm, not proof declarations. Caps: Lean -M7000, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax128 through the unchanged shared launcher. One scope at a time. Raw stdout, GNU time, SHA, dependency fingerprint and full axiom reports are retained per attempt. Admission logs are retained separately. No Kani invocation yet.',
'', 'The focused explicit headline/symbolic-root audit is pending reservation admission; J26201 already checks every candidate family declaration. Target not yet established.',
'', '## Candidate family modules', '', '| Module | Audited declarations | Backend Formatter module imported |', '|---|---:|---|']
for m in c['audited_modules']:lines.append(f"| `{m}` | {by[m]} | {'yes' if m in im['import_paths'] else 'no'} |")
lines+=['','## Every project importer of the Formatter module','']
lines += [f'- `{m}`' for m in sorted(im['import_paths'])]
(e/'FORMATTER-CLOSURE.md').write_text('\n'.join(lines)+'\n')
(e/'budget.json').write_text(json.dumps(dict(lean_budget=100,lean_attempts=2,kani_budget=10,kani_runs=0,admission_refusals=1,next_unused_env_j=26202),indent=2)+'\n')
print(len(rows),len(owners),len(by),len(bad))
