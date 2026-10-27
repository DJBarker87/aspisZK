from pathlib import Path
import json,re,hashlib,subprocess
E=Path('evidence/pv-op223-20261027');R=Path('docs/research/v8-r0-zk-20261009/lean');allowed={'propext','Classical.choice','Quot.sound'};rows=[];latest={}
for f in sorted(E.glob('[0-9][0-9][0-9][0-9][0-9].json')):
 d=json.loads(f.read_text());raw=d.get('axiom_output','');sets=[]
 for m in re.finditer(r"'([^']+)' depends on axioms: \[([^]]*)\]",raw,re.S):
  names=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',m[2]));sets.append(dict(declaration=m[1],axioms=sorted(names)))
 if d['exit_status']==0:assert all(set(x['axioms'])<=allowed for x in sets),(f,sets)
 snapshot=E/(f.stem+'-source.lean.txt');assert hashlib.sha256(snapshot.read_bytes()).hexdigest()==d['source_sha256']
 row={k:d[k] for k in ['attempt','module','source_revision','source_sha256','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps']};row['axioms']=sets;row['lean_submission_revision']=json.loads((E/(f.stem+'-submission.json')).read_text())['source_revision'];rows.append(row)
 if d['exit_status']==0:latest[d['module']]=row
for module,d in latest.items():
 p=R/(module+'.lean');d['matches_current_source']=hashlib.sha256(p.read_bytes()).hexdigest()==d['source_sha256']
t=json.loads((E/'TALLY.json').read_text());assert len(rows)==t['lean_charged'],(len(rows),t['lean_charged'])
summary=dict(branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),implementation_revision='6be26e38fddd78c4a97027689ffa329e4a8e8038',lean_budget=100,kani_budget=0,charged=len(rows),passed=sum(r['exit_status']==0 for r in rows),failed=sum(r['exit_status']!=0 for r in rows),refused_or_preflight_ids=[a['id'] for a in t['attempts'] if not a.get('charged')],latest_modules=latest,attempts=rows)
(E/'PROOF-RECEIPTS.json').write_text(json.dumps(summary,indent=2)+'\n')
print({k:v for k,v in summary.items() if k not in ['latest_modules','attempts']})
