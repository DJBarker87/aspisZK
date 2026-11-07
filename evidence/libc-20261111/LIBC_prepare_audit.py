from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
accepted={}
for p in sorted(E.glob('LIBC_L[0-9][0-9][0-9]/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit_status']==0 and j['kind']=='lean' and j['module'].startswith('LIBC_'):accepted[j['module']]=(p,j)
roots=[];matched=[]
for mod,(p,j) in accepted.items():
 src=E/(mod+'.lean')
 if not src.exists():continue
 h=hashlib.sha256(src.read_bytes()).hexdigest()
 assert j['source_hashes']['LIBC_generated/'+mod+'.lean']==h,(mod,'source differs from accepted receipt')
 code=src.read_text()
 names=re.findall(r'^(?:@\[[^\n]*\] )?theorem (\w+)',code,re.M)
 if not names:continue
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]
 roots += [ns+'.'+n for n in names]
 matched.append(dict(module=mod,receipt=str(p.relative_to(E)),sha256=h,roots=[ns+'.'+n for n in names]))
roots=sorted(set(roots))
old=json.loads((E/'LIBC_AUDIT_ROOTS.json').read_text()) if (E/'LIBC_AUDIT_ROOTS.json').exists() else {'roots':[],'groups':[]}
assert set(old['roots'])<=set(roots),'An existing audited root disappeared'
added=[r for r in roots if r not in old['roots']]
groups=old['groups']+[added[i:i+40] for i in range(0,len(added),40)]
(E/'LIBC_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=1)+'\n')
(E/'LIBC_AUDIT_MODULES.json').write_text(json.dumps([['LIBC_COMBINED_IMPORT'] for _ in groups],indent=1)+'\n')
(E/'LIBC_ACCEPTED_SOURCES.json').write_text(json.dumps(matched,indent=1)+'\n')
print('Own roots',len(roots),'groups',len(groups),'modules',len(matched))
