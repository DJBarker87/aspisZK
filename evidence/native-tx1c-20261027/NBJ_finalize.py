from pathlib import Path
import sys,json,hashlib,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBJ_host as h
subprocess.run([sys.executable,str(E/'NBJ_collect.py')],check=True)
expected=json.loads((E/'NBJ_LOCAL_SOURCE_AUDIT.json').read_text())['files']
r=h.remote_py(f'''from pathlib import Path
import json,hashlib,os,subprocess,shutil
b=Path({h.B!r});s=b/'NBJ_src';out={{}}
expected={expected!r}
for n,digest in expected.items():
 data=(s/n).read_bytes()
 for file,mod in [('candidate.rs','NBJ_keys'),('multiproof.rs','NBJ_multiproof')]:
  if n=='crates/aspis-r1-cost-probe/src/'+file:
   reg=('\\n#[cfg(kani)]\\n#[path="'+mod+'.rs"]\\nmod '+mod+';\\n').encode()
   assert data.endswith(reg);data=data[:-len(reg)]
 assert hashlib.sha256(data).hexdigest()==digest,n
out['frozen_source_files']=len(expected);out['frozen_sources_equal']=True
extras=[str(p.relative_to(s)) for root in [s/'crates',s/'programs'] for p in root.rglob('*') if p.is_file() and str(p.relative_to(s)) not in expected]
assert sorted(extras)==['crates/aspis-r1-cost-probe/src/NBJ_keys.rs','crates/aspis-r1-cost-probe/src/NBJ_multiproof.rs'],extras
out['harness_extras']=extras
for label,root in [('cache',{h.CACHE!r}),('coherent',{h.C!r}),('aeneas',{(h.C+'/objects/Aeneas')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
p=Path({(h.C+'/objects/Aeneas.olean')!r});out['aeneas'][str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
processes=subprocess.check_output(['ps','-eo','pid=,args='],text=True).splitlines();live=[]
for row in processes:
 pid,_,args=row.strip().partition(' ')
 if int(pid) in [os.getpid(),os.getppid()]:continue
 if {h.B!r} in args and any(t in args for t in ['cargo-kani kani',' kani-compiler ',' cbmc ','S2W_run_host.py NBJ_']):live.append(row)
assert not live,live
out['live_owned_builds']=live;out['private_objects']=[str(p) for p in b.rglob('*.olean')];assert not out['private_objects']
out['removed']={{}}
for name in ['NBJ_target','NBJ_tmp']:
 p=b/name
 if p.exists():
  out['removed'][str(p)]=len(list(p.rglob('*')));shutil.rmtree(p)
out['persistent_cache_retained']={h.CACHE!r}
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
(E/'NBJ_TERMINAL_HOST.json').write_text(r.stdout)
start=json.loads((E/'NBJ_INITIAL_HOST_PINS.json').read_text());end=json.loads(r.stdout)
for group in ['cache','coherent','aeneas']:
 assert all(end[group].get(p)==v for p,v in start[group].items()),'STOP changed '+group
print('Unchanged initial objects', {g:len(start[g]) for g in ['cache','coherent','aeneas']})
