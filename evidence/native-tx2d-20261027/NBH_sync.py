"""Sync only own scratch cfg(kani) module additions, after fresh admission."""
import importlib.util,sys,json,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('NBH_native',E/'NBH_native.py');m=importlib.util.module_from_spec(sp);saved=sys.argv;sys.argv=['sync','none'];sp.loader.exec_module(m);sys.argv=saved
attempt=sys.argv[1];m.admit(attempt)
patch=(E/'NBH_harness.patch').read_text();files={};current=None
for line in patch.splitlines(True):
 if line.startswith('+++ '):
  name=line[6:].strip(); current=name if '/NBH_' in name else None
  if current:files[current]=''
 elif current and line.startswith('+'):files[current]+=line[1:]
parents={}
for name,child in [('pair_terminal.rs','NBH_after'),('pair_tree_profile.rs','NBH_live'),('verifier_registry.rs','NBH_registry'),('format.rs','NBH_format'),('pair_forest_terminal.rs','NBH_terminal'),('pair_forest_accounts.rs','NBH_accounts')]:
 path='crates/aspis-statement/src/pool_v1/'+name
 old=subprocess.check_output(['git','show',m.REV+':'+path],text=True)
 marker='\n#[cfg(kani)]\n#[path="'+child+'.rs"]\nmod '+child+';\n'
 parents[path]=dict(original=old,marker=marker)
payload=json.dumps(dict(files=files,parents=parents))
payload_path=E/(attempt+'-payload.json');payload_path.write_text(payload)
for retry in range(11):
 result=subprocess.run(['scp','-q',str(payload_path),m.H+':'+m.B+'/'+payload_path.name],capture_output=True,text=True)
 with (E/(attempt+'-scp.jsonl')).open('a') as log:log.write(json.dumps(dict(retry=retry,exit=result.returncode,stderr=result.stderr))+'\n')
 if result.returncode==0:break
 if result.returncode!=255 or retry==10:raise SystemExit('STOP own payload transport')
 m.time.sleep(60)
r=m.py(f'''from pathlib import Path
import json,hashlib
x=json.loads(Path({(m.B+'/'+payload_path.name)!r}).read_text()); b=Path({(m.B+'/NBH_src')!r}); hashes={{}}
for name,values in x['parents'].items():
 p=b/name;old=values['original']; marker=values['marker']; assert p.read_text() in [old,old+marker],name
 p.write_text(old+marker);hashes[name]=hashlib.sha256(p.read_bytes()).hexdigest()
for name,source in x['files'].items():
 p=b/name;p.write_text(source);hashes[name]=hashlib.sha256(p.read_bytes()).hexdigest()
print(json.dumps(hashes,indent=2))
''');assert r.returncode==0,r.stdout+r.stderr
(E/(attempt+'-hashes.json')).write_text(r.stdout)
