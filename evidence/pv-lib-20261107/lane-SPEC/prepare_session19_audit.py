"""Freeze own roots; retain the strict walker and collector byte-for-byte."""
from pathlib import Path
import json,hashlib,re
L=Path(__file__).resolve().parent;R=L.parents[2]
modules=[];roots=[]
for a in list(range(55781,55790))+list(range(56200,56207)):
 r=json.loads((L/f'receipt-{a}.json').read_text())
 if not r['accepted'] or 'Print19' in r['target']:continue
 m=r['target'];assert m not in modules;modules.append(m)
 s=(R/'lean'/(m+'.lean')).read_text()
 assert hashlib.sha256(s.encode()).hexdigest()==r['source_sha256']
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots += [ns+'.'+name for name in re.findall(r'^(?:def|abbrev|theorem|structure|inductive) (\w+)',s,re.M)]
old=(R/'lean/PV_LIB_SPEC_RawAuditSession17.lean').read_text();a=old.index('    (#[');b=old.index('\n  let env ←',a)
arrays='    (#['+', '.join('`'+m for m in modules)+'],\n     #['+', '.join('`'+r for r in roots)+'])'
s=old[:a]+arrays+old[b:]
(R/'lean/PV_LIB_SPEC_RawAuditSession19.lean').write_text(s)
record={'count':len(roots),'modules':modules,'roots':roots,'driver_sha256':hashlib.sha256(s.encode()).hexdigest(),'collector_suffix_sha256':hashlib.sha256(s[b-len(old)+len(s):].encode()).hexdigest()}
assert old[b:]==s[s.index('\n  let env ←'):]
record['collector_suffix_sha256']=hashlib.sha256(old[b:].encode()).hexdigest()
(L/'SESSION19_RAW_ROOTS.json').write_text(json.dumps(record,indent=2)+'\n')
s=(L/'host_audit_s17.py').read_text().replace('55493','55496').replace('Session17','Session19').replace('session17','session19').replace('host_audit_s17.py','host_audit_s19.py')
s=s.replace("for c in ['W3_COMPAT','W4','LANEA']:","for c in ['ACTIVE19']:").replace("[('w3','Session19','J-w3.json')]","[('active19','Session19','J-active19.json')]").replace("for c in ['w3']:","for c in ['active19']:")
s=s.replace('isolated W3 cohort','adopted c18-s16 compatible cohort')
(L/'host_audit_s19.py').write_text(s)
s=(L/'archive_session17.py').read_text().replace('55493','55496').replace('SESSION17','SESSION19').replace("['w3']","['active19']")
# Historical diagnostic flags are not release claims for the new audit.
s=s.replace('callback_byte_suffix_installed=True,canonical_thread_word_repaired=True,scope_u8_repaired=True,physical_stack_pairing_proved=False,','callback_model_repair_adopted=True,original85_transport=True,full_execution_preserved_through141=True,')
(L/'archive_session19.py').write_text(s)
print(json.dumps({'modules':len(modules),'roots':len(roots)}))
