from pathlib import Path
import subprocess,json,sys,shlex,hashlib
import NCX_transport as t
E=t.E;B=t.B
def launch(a,kind,target,files,command,sources,timeout=180,extra=None):
 if (E/'NCX_HOLD').exists():raise SystemExit('own queue held for shape review; no launch')
 assert not (E/a).exists(),'attempt already used'
 if kind in ['kani','lean']:
  count=sum(json.loads(l)['kind']==kind for l in (E/'NCX_ATTEMPTS.jsonl').read_text().splitlines());assert count<(40 if kind=='kani' else 60),'budget exhausted'
 assert not (E/'NCX_ACTIVE.json').exists(),'unresolved submitted attempt'
 t.admit(a)
 env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NCX_tmp',CARGO_TARGET_DIR=B+'/NCX_target',LEAN_PATH=B+'/NCX_objects:/home/dombarker/project-offloads/codex-cx-decref-cache-20261028:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
 cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=env,timeout=timeout,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'frozen_source':t.REV},expected_time=('Optimized compilation, then solver gate '+target if kind=='kani' else 'One focused '+kind+' target '+target))
 if kind=='lean':
  import re
  imports=[i for source in files.values() for i in re.findall(r'^import (\S+)',source,re.M)]
  query='''from pathlib import Path
import json,hashlib
roots=ROOTS
x={}
for n in IMPORTS:
 p=next((Path(root)/(n.replace('.','/')+'.olean') for root in roots if (Path(root)/(n.replace('.','/')+'.olean')).is_file()),None)
 if p is not None:x[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(x))
'''.replace('ROOTS',repr(env['LEAN_PATH'].split(':'))).replace('IMPORTS',repr(imports))
  r=t.py(query);assert r.returncode==0,r.stderr
  cfg['deps_fingerprint']['direct_import_objects']=json.loads(r.stdout)
  cfg['deps_fingerprint']['cache_import_manifest_sha256']=hashlib.sha256((E/'NCX_SETUP_PINS.json').read_bytes()).hexdigest()
  cfg['deps_fingerprint']['selected_objects']={p:dict(path=p,sha256=h) for p,h in json.loads((E/'NCX_SETUP_PINS.json').read_text())['library'].items()}
 if extra:cfg.update(extra)
 files[a+'.json']=json.dumps(cfg,indent=2)
 for n,s in files.items():
  p=E/a/'sources'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 # Snapshot directory preexists locally but host attempt is unique.
 t.upload(files)
 if kind=='lean':
  r=t.py('from pathlib import Path; (Path('+repr(B+'/NCX_objects/'+target)+').parent).mkdir(parents=True,exist_ok=True)');assert r.returncode==0,r.stderr
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 (E/'NCX_ACTIVE.json').write_text(json.dumps(dict(attempt=a)))
 r=t.ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+shlex.quote(a+'.json'),submitted=True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 rc=collect(a)
 if kind=='kani':
  import difflib
  patch=''
  for name,body in files.items():
   if not name.startswith('NCX_src/'):continue
   rel=name[len('NCX_src/'):]
   old=subprocess.run(['git','show',t.REV+':'+rel],capture_output=True,text=True)
   before=old.stdout if old.returncode==0 else ''
   patch+=''.join(difflib.unified_diff(before.splitlines(True),body.splitlines(True),fromfile='a/'+rel if before else '/dev/null',tofile='b/'+rel))
   (E/a/'sources'/name).unlink()
  (E/a/'sources'/'NCX_harness.patch').write_text(patch)
 (E/'NCX_ACTIVE.json').unlink()
 print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
 print((E/a/'stdout.log').read_text()[-2300:],flush=True)
 return rc
def collect(a):
 r=t.py(f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph.json',a+'-metadata.stderr','NCX_EXTRACTION_PINS.json']!r}
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).exists()}}))
''');assert r.returncode==0,r.stderr
 x=json.loads(r.stdout)
 for n,s in x.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 assert a+'/receipt.json' in x,'STOP unresolved submitted attempt; never resubmit'
 rc=json.loads(x[a+'/receipt.json'])
 with (E/'NCX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
 return rc
