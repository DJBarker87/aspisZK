from pathlib import Path
import sys,json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBY_host as h
assert len(list(E.glob('NBY_K[0-9][0-9][0-9]/receipt.json')))==80,'Finish authorized budget first'
frozen=json.loads((E/'NBY_FROZEN_SOURCE_PINS.json').read_text())['files'];hashes={n:v['sha256'] for n,v in frozen.items()}
r=h.remote_py(f'''from pathlib import Path
import json,hashlib,subprocess,re,shutil
b=Path({h.B!r});s=b/'NBY_src'
rows=subprocess.check_output(['ps','-eo','args='],text=True).splitlines()
live=[x for x in rows if re.match(r'^(?:/usr/bin/)?python3 S2W_(?:run|lean)_host[.]py NBY_',x.strip())];assert not live,live
out={{'live':live,'pins':{{}},'changed_sources':{{}},'cleanup':{{}},'launchers':{{}}}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{h.C!r}),('aeneas',{(h.C+'/objects/Aeneas')!r})]:
 out['pins'][label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
p=Path({(h.C+'/objects/Aeneas.olean')!r});out['pins']['aeneas'][str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
known={hashes!r}
for p in s.rglob('*'):
 if p.is_file() and p.suffix in ['.rs','.lean']:
  n=str(p.relative_to(s));data=p.read_bytes()
  allowed=n in known or n in ['KMX_stubs.rs','KMX_CopyMeaning.lean','KMX_native.rs'] or n.startswith('crates/aspis-r1-cost-probe/src/NBY_') or n.startswith('crates/aspis-r1-cost-probe/src/NBV_')
  if allowed and hashlib.sha256(data).hexdigest()!=known.get(n):out['changed_sources'][n]=data.decode()
for rp in sorted(b.glob('NBY_[KL][0-9][0-9][0-9]/receipt.json')):
 j=json.loads(rp.read_text());cg=Path(j['cgroup']);procs=(cg/'cgroup.procs').read_text().split() if cg.exists() else [];assert not procs,(j['attempt'],procs)
 out.setdefault('terminal_scopes',{{}})[j['attempt']]={{'cgroup':str(cg),'exists':cg.exists(),'processes':procs}}
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 p=b/name;old=Path('/home/dombarker/project-offloads/codex-cx-native-tx1e-20261028')/name
 v=hashlib.sha256(p.read_bytes()).hexdigest();assert v==hashlib.sha256(old.read_bytes()).hexdigest();out['launchers'][name]=v
for name in ['NBY_target','NBY_tmp']:
 p=b/name;assert p.parent==b and name in ['NBY_target','NBY_tmp']
 if p.exists():
  assert p.is_dir() and not p.is_symlink()
  out['cleanup'][name]={{'files':sum(x.is_file() for x in p.rglob('*')),'bytes':sum(x.stat().st_size for x in p.rglob('*') if x.is_file())}}
  shutil.rmtree(p)
  out['cleanup'][name]['removed']=not p.exists()
assert Path({h.CACHE!r}).is_dir();out['cache_retained']=True
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout);changed=out.pop('changed_sources');(E/'NBY_FINAL_HOST_PINS.json').write_text(json.dumps(out,indent=2)+'\n')
initial=json.loads((E/'NBY_INITIAL_HOST_PINS.json').read_text());comparison={}
for label,old in initial.items():
 if not isinstance(old,dict):continue
 now=out['pins'][label];bad=[n for n,v in old.items() if now.get(n)!=v];assert not bad,(label,bad)
 comparison[label]={'initial':len(old),'final':len(now),'changed_existing':bad,'new':sorted(set(now)-set(old))}
(E/'NBY_PIN_COMPARISON.json').write_text(json.dumps(comparison,indent=2)+'\n')
patch=''
for n,s in sorted(changed.items()):
 old=(R/n).read_text() if n in frozen else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NBY_COMPLETE_HARNESS.patch').write_text(patch)
pins={'path':str(E/'NBY_COMPLETE_HARNESS.patch'),'sha256':hashlib.sha256(patch.encode()).hexdigest(),'size':len(patch.encode()),'source_files':{n:{'sha256':hashlib.sha256(s.encode()).hexdigest(),'size':len(s.encode())} for n,s in changed.items()}}
(E/'NBY_HARNESS_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
for n,v in frozen.items():assert hashlib.sha256((R/n).read_bytes()).hexdigest()==v['sha256'],n
p=subprocess.run(['git','apply','--check',str(E/'NBY_COMPLETE_HARNESS.patch')],cwd=R,text=True,capture_output=True)
(E/'NBY_PATCH_CHECK.json').write_text(json.dumps({'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr},indent=2)+'\n');assert p.returncode==0,p.stderr
print(json.dumps({'cache_retained':True,'existing_object_changes':0,'patch_files':len(changed),'patch_sha256':pins['sha256'],'cleanup':out['cleanup']}))
