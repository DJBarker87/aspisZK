"""Freeze explicit NEW roots; reuse strict collector/walker without changes."""
from pathlib import Path
import json,hashlib,re
L=Path(__file__).resolve().parent;R=L.parents[2]
modules=[];roots=[]
for a in list(range(55455,55490))+list(range(55500,55525)):
 r=json.loads((L/f'receipt-{a}.json').read_text())
 if not r['accepted']:continue
 m=r['target'];assert m not in modules;modules.append(m)
 s=(R/'lean'/(m+'.lean')).read_text();assert hashlib.sha256(s.encode()).hexdigest()==r['source_sha256']
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 decls=re.findall(r'^(?:def|abbrev|theorem|structure|inductive) (\w+)',s,re.M)
 roots += [ns+'.'+name for name in decls]
old=(R/'lean/PV_LIB_SPEC_RawAuditSession14.lean').read_text();a=old.index('    (#[');b=old.index('\n  let env ←',a)
arrays='    (#['+', '.join('`'+m for m in modules)+'],\n     #['+', '.join('`'+r for r in roots)+'])'
s=old[:a]+arrays+old[b:];p=R/'lean/PV_LIB_SPEC_RawAuditSession15.lean';p.write_text(s)
record={'count':len(roots),'modules':modules,'roots':roots,'driver_sha256':hashlib.sha256(s.encode()).hexdigest(),'collector_suffix_sha256':hashlib.sha256(s[b:].encode()).hexdigest()}
# The new array has a different length, so obtain suffix from its actual marker.
record['collector_suffix_sha256']=hashlib.sha256(s[s.index('\n  let env ←'):].encode()).hexdigest()
(L/'SESSION15_RAW_ROOTS.json').write_text(json.dumps(record,indent=2)+'\n')
for source,dest in [('host_audit_s14.py','host_audit_s15.py'),('archive_session14.py','archive_session15.py')]:
 text=(L/source).read_text().replace('55490','55491').replace('Session14','Session15').replace('SESSION14','SESSION15').replace('session14','session15').replace('host_audit_s14.py','host_audit_s15.py')
 (L/dest).write_text(text)
print(json.dumps({'modules':len(modules),'roots':len(roots)}))
