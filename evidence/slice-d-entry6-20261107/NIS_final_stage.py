from NIS_formal import *
modules=['NIS_AdmissionSdk','NIS_SnapshotAbi','NIS_SdkReads','NIS_AbiFrame','NIS_EntryPrefixes','NIS_OwnedHeaders','NIS_Distinct3','NIS_Tx2Boundary','NIS_DigestCarrier','NIS_PublicCarrier','NIS_Tx1Boundary']
(E/'NIS_FINAL_IMPORTS.json').write_text(json.dumps(modules,indent=1)+'\n')
p=E/'NIS_COMBINED_IMPORT.lean';base=p.read_text();base='\n'.join(x for x in base.splitlines() if x not in ['import '+m for m in modules])+'\n';ls=base.splitlines(True);i=next(i for i,l in enumerate(ls) if not l.startswith('import '));p.write_text(''.join(ls[:i])+''.join('import '+m+'\n' for m in modules)+''.join(ls[i:]))
r=json.loads((E/'NIS_AUDIT_ROOTS.json').read_text());seen=set(sum(r['groups'],[]));new=[]
ats=[json.loads(l) for l in (E/'NIS_ATTEMPTS.jsonl').read_text().splitlines()]
for m in modules:
 h=sha((E/(m+'.lean')).read_bytes());ok=[x for x in ats if x.get('module')==m and x.get('exit_status')==0 and h in x.get('source_hashes',{}).values()];assert ok,m
 for s in ok[-1]['print_axioms']:
  name=re.match("'([^']+)'",s)[1]
  if name not in seen:seen.add(name);new.append(name)
if new:r['groups'].append(new)
(E/'NIS_AUDIT_ROOTS.json').write_text(json.dumps(r,indent=1)+'\n')
lines={x['module']:x for x in map(json.loads,(E/'NIS_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for p in E.glob('NIS_*.lean'):
 im=['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)
 lines[p.stem]={'module':p.stem,'imports':im}
(E/'NIS_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(lines[k])+'\n' for k in sorted(lines)))
rc=run('NIS_L058','lean','NIS_COMBINED_IMPORT');assert rc['exit_status']==0
files={n:(E/n).read_text() for n in ['NIS_AUDIT_ROOTS.json','NIS_EXPECTED_IMPORTS.jsonl','NIS_audit_one.py']};files['NIM_AUDIT_MODULES.json']=json.dumps([['NIS_COMBINED_IMPORT']])
for i,mode,name in [(59,'proof0','NIS_ProofDriver'),(60,'scan','NIS_ScanDriver')]:
 rc=run(f'NIS_L{i:03}','audit',mode,['python3','NIS_audit_one.py','NIS_native/'+name,mode],files)
 assert rc['exit_status']==0
 rr=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NIS_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NIS_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text() for p in paths}}))
''');assert rr.returncode==0,rr.stderr
 for n,t in json.loads(rr.stdout).items():
  p=E/('NIS_'+n)
  if n.endswith('.json'):p.write_text(t)
  else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
print('PASS_COMBINED_GROUP0_AND_SCAN; additional raw group requires NIS_audit_new_roots.py',flush=True)
