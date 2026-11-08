"""Freeze explicit NEW roots; reuse strict collector/walker without changes."""
from pathlib import Path
import json,hashlib,re
L=Path(__file__).resolve().parent;R=L.parents[2]
modules=[];roots=[]
for a in range(55116,55147):
 r=json.loads((L/f'receipt-{a}.json').read_text())
 if not r['accepted']:continue
 m=r['target'];assert m not in modules;modules.append(m)
 s=(R/'lean'/(m+'.lean')).read_text();assert hashlib.sha256(s.encode()).hexdigest()==r['source_sha256']
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 decls=re.findall(r'^(?:def|abbrev|theorem|structure|inductive) (\w+)',s,re.M)
 roots += [ns+'.'+name for name in decls]
old=(R/'lean/PV_LIB_SPEC_RawAuditSession11.lean').read_text();a=old.index('    (#[');b=old.index('\n  let env ←',a)
arrays='    (#['+', '.join('`'+m for m in modules)+'],\n     #['+', '.join('`'+r for r in roots)+'])'
s=old[:a]+arrays+old[b:];p=R/'lean/PV_LIB_SPEC_RawAuditSession12.lean';p.write_text(s)
record={'count':len(roots),'modules':modules,'roots':roots,'driver_sha256':hashlib.sha256(s.encode()).hexdigest(),'collector_suffix_sha256':hashlib.sha256(s[b:].encode()).hexdigest()}
# The new array has a different length, so obtain suffix from its actual marker.
record['collector_suffix_sha256']=hashlib.sha256(s[s.index('\n  let env ←'):].encode()).hexdigest()
(L/'SESSION12_RAW_ROOTS.json').write_text(json.dumps(record,indent=2)+'\n')
for source,dest in [('host_audit_s11.py','host_audit_s12.py'),('archive_session11.py','archive_session12.py')]:
 text=(L/source).read_text().replace('34993','55190').replace('Session11','Session12').replace('SESSION11','SESSION12').replace('session11','session12').replace('host_audit_s11.py','host_audit_s12.py')
 if source.startswith('archive'):
  text=text.replace('canonical_thread_word_repaired=True,','canonical_thread_word_repaired=True,scope_u8_repaired=True,physical_stack_pairing_proved=False,')
 (L/dest).write_text(text)
print(json.dumps({'modules':len(modules),'roots':len(roots)}))
