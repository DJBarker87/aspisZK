#!/usr/bin/env python3
"""Run exactly one focused command; invoked inside the admitted systemd scope."""
import hashlib,json,os,pathlib,subprocess,sys,time,shutil
base=pathlib.Path(__file__).resolve().parent
cfg=json.loads((base/sys.argv[1]).read_text())
manifest=json.loads((base/'cache-manifest.json').read_text())
new_objects={}
for source,expected in cfg.get('new_dependencies',{}).items():
 assert hashlib.sha256((base/source).read_bytes()).hexdigest()==expected,source
 for obj in (base/'objects').glob(pathlib.Path(source).stem+'.*'):
  new_objects[obj.name]={'sha256':hashlib.sha256(obj.read_bytes()).hexdigest(),'size':obj.stat().st_size}
cfg['new_dependency_objects']=new_objects
for module,item in manifest['modules'].items():
 if '/.elan/toolchains/' in item['path']:continue
 obj=base/'objects'/pathlib.Path(*module.split('.')).with_suffix('.olean')
 assert hashlib.sha256(obj.read_bytes()).hexdigest()==item['sha256'],module
for rel,item in json.loads((base/'companion-manifest.json').read_text()).items():
 assert hashlib.sha256((base/'objects'/rel).read_bytes()).hexdigest()==item['sha256'],rel
out=base/cfg['attempt'];out.mkdir(exist_ok=False)
for source in cfg['sources']: shutil.copyfile(base/source,out/(pathlib.Path(source).name+'.txt'))
rel=pathlib.Path('/sys/fs/cgroup')/next(l.split(':',2)[2].strip().lstrip('/') for l in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
limits={n:(rel/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},limits
env=os.environ.copy();env.update(cfg.get('env',{}))
start=time.monotonic()
with (out/'stdout.log').open('w') as log:
 r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),'timeout',str(cfg.get('timeout',180)),*cfg['command']],cwd=base,env=env,stdout=log,stderr=subprocess.STDOUT)
duration=time.monotonic()-start
log=(out/'stdout.log').read_text();tim=(out/'time.log').read_text()
def metric(name):
 return next((l.split(':',1)[1].strip() for l in tim.splitlines() if name in l),None)
receipt={**cfg,'exit_status':r.returncode,'wall_seconds':duration,'peak_rss_kib':metric('Maximum resident set size'),'swaps':metric('Swaps'),'cgroup':str(rel),'limits':limits,'cgroup_memory_peak_bytes':(rel/'memory.peak').read_text().strip(),'source_hashes':{f:hashlib.sha256((base/f).read_bytes()).hexdigest() for f in cfg['sources']},'deps_fingerprint':cfg.get('deps_fingerprint','Std from pinned Lean sysroot only'),'print_axioms':[l for l in log.splitlines() if 'axioms' in l or 'depends on axioms' in l] if cfg['kind']=='lean' else 'N/A: Kani'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2));print(log[-12000:]);sys.exit(r.returncode)
