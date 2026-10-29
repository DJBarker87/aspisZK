from pathlib import Path
import json
P=Path(__file__).parent;rows=json.loads((P/'claim-audit-dispositions.json').read_text());fps=json.loads((P/'formatter-footprints.json').read_text())+json.loads((P/'formatter-footprints-more.json').read_text());complete={x['id']:x for x in fps if not x['import_gaps']and not x['unresolved_project_constants']};out=[]
lines=['# fmt-1 disposition','', 'A carrier-name reference is not an executed formatting call. These are forensic constant-dependency scans of surviving object variants, with proof bodies included. They do not establish native call-cone or D159 observational adequacy. The five receipt-recovered roots additionally match the recorded object SHA. Exact paths and all variants are retained in the JSON evidence.','', '| Row | Closing theorem | Checked footprint | fmt-1 route |','|---|---|---|---|']
for r in rows:
 id=r['id'];f=complete.get(id)
 if id=='V270':check='scoped inventory audit; original nine root outputs standard-only';route='not a formatting semantics result'
 elif f:
  calls=[n for n in f['fmt_constants']if n!='Aeneas.Std.core.fmt.Error'];assert not calls
  check='no formatting functions; Error carrier only'if f['fmt_constants']else'no core.fmt constants'
  route='not applicable: no formatter-function reliance detected'
 else:
  check='missing closing object / incomplete import cone';route='UNRESOLVED; no (a)/(b)/(c) credit assigned'
 lines.append('| '+id+' | `'+str(r['theorem']or'inventory')+'` | '+check+' | '+route+' |');out.append(dict(id=id,theorem=r['theorem'],checked=id in complete,footprint=f.get('fmt_constants')if f else None,fmt1_route=route))
missing=[x['id']for x in out if not x['checked']and x['id']!='V270'];lines+=['','Complete recovered cones: '+str(len(complete))+'/56. Unresolved: '+', '.join(missing)+'.', '', 'No credited formatter-function user was demonstrated in the recovered cones, so no new (a), (b), or (c) certificate is claimed. Missing cones prevent an exhaustive claim that there are none. A clean printed axiom set alone is insufficient to fill those gaps.', '', 'The b3q arbitrary rejecting-writer/numeric-formatting instance is a **VIOLATION** of fmt-1 if used as an unconditional deployed formatter law: no guard (a), infallibility proof (b), or faithful state/error model (c) supports it. That diagnostic is quarantined, not a credited closure. Its standard-only literal-port refutation is not a use of Aeneas formatting semantics. V269 and the actual std/dependency closure stay open. Observable stderr/JSON/Debug paths need (c) or approved removal; a Unit carrier or successful Result supplies no such evidence.']
(P/'FMT1-CLASSIFICATION.md').write_text('\n'.join(lines)+'\n');(P/'fmt1-dispositions.json').write_text(json.dumps(out,indent=1));print('complete',len(complete),'missing',missing)
