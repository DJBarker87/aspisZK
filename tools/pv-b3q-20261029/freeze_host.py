from pathlib import Path
import json,hashlib,re
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();f=json.loads((H/'frozen-manifest.json').read_text());records={}
for p in H.glob('lean-*/receipt/receipt.json'):
 r=json.loads(p.read_text());records.setdefault(r.get('module'),[]).append((p,r))
rows=[];allowed={'propext','Classical.choice','Quot.sound'}
for source in f['sources']:
 p=H/'lean'/(source['module']+'.lean');assert sha(p)==source['sha256'],source['module']
 if source['module']in ['PV_B3Q_Combined','PV_B3Q_Axioms','PV_B3Q_Manifest']:continue
 choices=[(p,r)for p,r in records[source['module']]if r['exit_status']==0 and r['source_sha256']==source['sha256']];assert len(choices)==1,(source,choices)
 p,r=choices[0];log=(p.parent/'stdout.log').read_text();audits=[]
 for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S):
  found={a.strip()for a in axioms.split(',')if a.strip()};assert found<=allowed,(source['module'],name,found);audits.append(dict(name=name,axioms=sorted(found)))
 obj=H/'lean-objects'/(source['module']+'.olean');assert obj.exists()
 rows.append(dict(**source,attempt=r['attempt'],receipt=str(p),object_sha256=sha(obj),source_revision=r['source_revision'],axioms=audits))
cache=json.loads((H/'cache-verification.json').read_text());assert not cache['mismatches']
for m,r in cache['objects'].items():
 assert sha(Path(r['object']))==r.get('object_sha256',r.get('sha256')),(m,'changed inherited object')
x=dict(status='pass',accepted_source_count=len(rows),sources=rows,excluded_quarantined=['PV_B3Q_FormatCounterexample: actual pinned formatter depends on core.fmt.Formatter'],inherited_cohort_checked=len(cache['objects']),next_targets=[['PV_B3Q_Combined',70297],['PV_B3Q_Axioms',70298],['PV_B3Q_Manifest',70299]],external_preflight='preflight.json: 5673 objects verified before first compile',no_rebuild_of_unchanged_dependencies=True)
(H/'preaudit-freeze.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(status='pass',accepted_sources=len(rows),inherited_objects=len(cache['objects']))))
