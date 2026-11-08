"""Freeze explicit session17 new roots; unchanged strict walker/collector."""
from pathlib import Path
import hashlib,json,re
L=Path(__file__).resolve().parent;R=L.parents[2]
modules=[];roots=[]
for a in range(55574,55589):
 r=json.loads((L/f'receipt-{a}.json').read_text())
 if not r['accepted']:continue
 m=r['target'];assert m not in modules;modules.append(m)
 s=(R/'lean'/(m+'.lean')).read_text()
 assert hashlib.sha256(s.encode()).hexdigest()==r['source_sha256']
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots += [ns+'.'+name for name in re.findall(r'^(?:def|abbrev|theorem|structure|inductive) (\w+)',s,re.M)]
old=(R/'lean/PV_LIB_SPEC_RawAuditSession16.lean').read_text();a=old.index('    (#[');b=old.index('\n  let env ←',a)
arrays='    (#['+', '.join('`'+m for m in modules)+'],\n     #['+', '.join('`'+r for r in roots)+'])'
s=old[:a]+arrays+old[b:]
(R/'lean/PV_LIB_SPEC_RawAuditSession17.lean').write_text(s)
record={'count':len(roots),'modules':modules,'roots':roots,'driver_sha256':hashlib.sha256(s.encode()).hexdigest(),'collector_suffix_sha256':hashlib.sha256(s[s.index('\n  let env ←'):].encode()).hexdigest()}
(L/'SESSION17_RAW_ROOTS.json').write_text(json.dumps(record,indent=2)+'\n')
for src,dst in [('host_audit_s16.py','host_audit_s17.py'),('archive_session16.py','archive_session17.py')]:
 text=(L/src).read_text().replace('55492','55493').replace('Session16','Session17').replace('SESSION16','SESSION17').replace('session16','session17').replace('host_audit_s16.py','host_audit_s17.py')
 (L/dst).write_text(text)
print(json.dumps({'modules':len(modules),'roots':len(roots)}))
