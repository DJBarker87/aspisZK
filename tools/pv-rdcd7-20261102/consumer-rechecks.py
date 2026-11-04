"""Assemble exact affected consumer dispositions from existing receipts/queries."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
projection=json.load(open(E/'consumer-audit-projection.json'));queries=set(projection['queries']);rows=[]
for m in projection['modules']:
 p=L/(m+'.lean');h=hashlib.sha256(p.read_bytes()).hexdigest();matches=[]
 for r in E.glob('lean-*/receipt.json'):
  j=json.load(open(r))
  if j.get('module')=='R1Z/'+m and j.get('source_sha256')==h and j['exit']==0:matches.append(str(r.relative_to(E)))
 rows.append(dict(consumer=m,source_sha256=h,disposition='focused corrected-model compile',receipts=matches,status='PASS' if matches else 'PENDING'))
audit=[]
for m in ['PV_RDCD4_FinalAudit','PV_RDCD5_FinalAudit']:
 s=(L/(m+'.lean')).read_text();affected=sorted(set(re.findall(r'^#(?:check @|print axioms )(R1Z\.\S+)',s,re.M))&queries)
 # Every queried member of an affected declaration namespace must be covered.
 namespaces={q.rsplit('.',1)[0] for q in queries}
 allq=set(re.findall(r'^#(?:check @|print axioms )(R1Z\.\S+)',s,re.M))
 assert {q for q in allq if q.rsplit('.',1)[0] in namespaces}<=queries,m
 audit.append(dict(consumer=m,source_sha256=hashlib.sha256(s.encode()).hexdigest(),affected_queries=affected,disposition='Exact affected declaration type/axiom projection; unrelated historical suite not rerun'))
unchanged=[]
for m in ['PV_RDCD4_SliceRange194','PV_RDCD5_BufferSource','PV_RDCD5_V233','PV_RDCD5_V236','PV_RDCD4_FocusedReplay','PV_RDCD4_FrozenManifest']:
 p=L/(m+'.lean');old=subprocess.check_output(['git','show','a9aa230d1e:'+str(p.relative_to(R))],cwd=R);assert p.read_bytes()==old,m
 unchanged.append(dict(consumer=m,source_sha256=hashlib.sha256(old).hexdigest(),disposition='Unchanged source; bounded helper/success-only law or no owned-parser declaration dependency; historical row credit retained at its original revision'))
out=dict(status='PASS focused source consumers' if all(x['status']=='PASS' for x in rows) else 'PENDING focused source consumers',focused=rows,audit_query_projections=audit,unchanged=unchanged,exact_replay_projection='consumer-audit-projection.json',transitive_audit_wrappers=['PV_RDCD4_FocusedReplay','PV_RDCD4_FrozenManifest','PV_RDCD5_FocusedReplay','PV_RDCD5_FrozenManifest'],historical_tools=['tools/pv-rdcd4-20261029/prepare-final-replay.py','tools/pv-rdcd5-20261101/prepare-audits.py'],qualification='Historical generators are source/query text consumers only and are not rerun. Current census tools have no parser runtime result. Other branches are read only; source-variant coverage is retained by the three census files and CONSUMERS.md. Final projection/raw audit gates separately required.')
(E/'CONSUMER-RECHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],sum(x['status']=='PASS' for x in rows),'/',len(rows),'focused modules')
