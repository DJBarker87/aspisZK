#!/usr/bin/env python3
"""Owned copy of the shared S2W_run_host.py: run exactly one focused command inside the admitted scope.
Only change: the expected cgroup limits come from the config ('expected_limits') instead of the fixed 6G/8G pair,
because the PCO brief caps extraction scopes at MemoryHigh=3G / MemoryMax=4G (Lean scopes keep 6G/8G).
All other behaviour is byte-for-byte the S2W logic."""
import hashlib,json,os,pathlib,subprocess,sys,time,re
base=pathlib.Path(__file__).resolve().parent
cfg=json.loads((base/sys.argv[1]).read_text())
out=base/cfg['attempt'];out.mkdir(exist_ok=False)
rel=pathlib.Path('/sys/fs/cgroup')/next(l.split(':',2)[2].strip().lstrip('/') for l in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
limits={n:(rel/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits==cfg['expected_limits'],(limits,cfg['expected_limits'])
assert limits['memory.swap.max']=='0'
env=os.environ.copy();env.update(cfg.get('env',{}))
for f in cfg['sources']:
 p=base/f; target=out/'sources'/f; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(p.read_bytes())
if cfg['kind']=='lean' and 'selected_objects' in cfg['deps_fingerprint']:
 for obj in cfg['deps_fingerprint']['selected_objects'].values():
  assert hashlib.sha256(pathlib.Path(obj['path']).read_bytes()).hexdigest()==obj['sha256'],obj['path']
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for c in iter(lambda:f.read(1<<20),b''):h.update(c)
 return h.hexdigest()
def watch(p):
 p=pathlib.Path(p)
 if not p.exists():return None
 st=p.stat();return dict(path=str(p),size=st.st_size,mtime=st.st_mtime,sha256=sha(p))
llbc_before=watch(cfg['llbc_watch']) if cfg.get('llbc_watch') else None
def fpsnap(name):
 if not cfg.get('fingerprint_dir'):return None
 fp={};root=pathlib.Path(cfg['fingerprint_dir'])
 if root.is_dir():
  for q in sorted(root.rglob('*')):
   if q.is_file():fp[str(q.relative_to(root))]=sha(q)
 (out/name).write_text(json.dumps(dict(dir=str(root),n=len(fp),files=fp),indent=0,sort_keys=True))
 return dict(n=len(fp),summary_sha256=hashlib.sha256(json.dumps(fp,sort_keys=True).encode()).hexdigest())
fp_before=fpsnap('target_fingerprints_before.json')
start=time.monotonic()
with (out/'stdout.log').open('w') as log:
 r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),'timeout',str(cfg.get('timeout',180)),*cfg['command']],cwd=base,env=env,stdout=log,stderr=subprocess.STDOUT)
duration=time.monotonic()-start
post={}
if cfg.get('llbc_watch'):post['llbc_stable_before']=llbc_before;post['llbc_stable_after']=watch(cfg['llbc_watch'])
post['target_fingerprints_before']=fp_before;post['target_fingerprints_after']=fpsnap('target_fingerprints.json')
(out/'post_watch.json').write_text(json.dumps(post,indent=1))
log=(out/'stdout.log').read_text();tim=(out/'time.log').read_text()
def metric(name):
 return next((l.split(':',1)[1].strip() for l in tim.splitlines() if name in l),None)
receipt={**cfg,'post':post,'exit_status':r.returncode,'wall_seconds':duration,'peak_rss_kib':metric('Maximum resident set size'),'swaps':metric('Swaps'),'cgroup':str(rel),'limits':limits,'cgroup_memory_peak_bytes':(rel/'memory.peak').read_text().strip(),'source_hashes':{f:hashlib.sha256((out/'sources'/f).read_bytes()).hexdigest() for f in cfg['sources']},'deps_fingerprint':cfg.get('deps_fingerprint','Std from pinned Lean sysroot only'),'print_axioms':re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log) if cfg['kind']=='lean' else 'N/A: '+cfg['kind']}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(log[:700]+'\n...\n'+log[-1800:]);sys.exit(r.returncode)
