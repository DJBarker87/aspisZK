from pathlib import Path
import json,collections
E=Path('evidence/pv-dict2-20261027');S=Path('docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026')
d=json.loads((S/'quotient231/entries.json').read_text());ledger={r['id']:r for r in json.loads(Path('evidence/privacy-recount-20261026/recount3/rows3.json').read_text())};rows=[]
for r in d['functions']:
 row=dict(r);lr=ledger.get(r.get('research_ledger_row'))
 row['entry_kind']='open callback' if r['status']=='OPEN' else ('inherited selected body' if r['inherited_source_selected'] else 'installed selector equation')
 if lr:row['recount3']={k:lr.get(k) for k in ['id','recount3_status','baseline_status','theorem','rationale','residual_fields']}
 row['deployed_discharge_claimed']=False;rows.append(row)
(E/'entry-classification.json').write_text(json.dumps(dict(source=str(S/'quotient231/entries.json'),denominators=d['after'],rows=rows,qualification='Source selection is not a universal law of an arbitrary ExternalFuns/native instance; imports and installed equations do not remove deployed endpoint premises.'),indent=2)+'\n')
print(collections.Counter(r['entry_kind'] for r in rows));print('required',collections.Counter(r['entry_kind'] for r in rows if r['required_by_source_bound']))
