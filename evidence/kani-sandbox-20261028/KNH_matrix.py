from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent
h=json.loads((E/'KNH_HARNESS_RESULTS.json').read_text())
table=json.loads(Path('evidence/kani-mitig-20261028/KMX_CONFIGURATION_MAP.json').read_text())
by={(r['attempt'],r['harness']):r for r in h};rows=[]
for a in ['KNH_N039','KNH_N040','KNH_O039']:
 for c in table:
  pos=c['expected']['harness'].split('::')[-1];neg=c['negative']['harness'].split('::')[-1]
  if a in ['KNH_N040','KNH_O039']:
   split=next(r for r in json.loads((E/'KNH_SPLIT_MAP.json').read_text()) if r['config']['id']==c['config']['id'])
   pos=split['harnesses']['correct'];neg=split['harnesses']['wrong']
  p=by.get((a,pos),dict(result='MISSING'));n=by.get((a,neg),dict(result='MISSING'))
  rows.append(dict(attempt=a,config=c['config'],correct=p,wrong=n,classification='EXPECTED_PAIR' if p['result']=='PASS' and n['result']=='FAIL' else 'FALSE_PASS_PAIR' if p['result']=='FAIL' and n['result']=='PASS' else 'UNRESOLVED_OR_OTHER'))
(E/'KNH_COPY_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
for a in ['KNH_N039','KNH_N040','KNH_O039']:print(a,dict(collections.Counter(r['classification'] for r in rows if r['attempt']==a)))
