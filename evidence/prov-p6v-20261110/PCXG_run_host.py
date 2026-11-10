#!/usr/bin/env python3
"""PCXG host side (derived from PCXF_run_host.py / S2W_run_host.py): runs the steps of one admitted scope sequentially.
Each step is one Lean process with its own timeout (180 s) and its own stdout/time log; stops at the first non-zero exit.
Limits are read from the cgroup and must equal the config's expected_limits (6G/8G, swap 0, pids 64)."""
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
 p=base/f;t=out/'sources'/f;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(p.read_bytes())
for obj in cfg['deps_fingerprint'].get('selected_objects',{}).values():
 assert hashlib.sha256(pathlib.Path(obj['path']).read_bytes()).hexdigest()==obj['sha256'],obj['path']
def metric(tim,name):
 return next((l.split(':',1)[1].strip() for l in tim.splitlines() if name in l),None)
steps=[];t_all=time.monotonic();worst=0;rc=0
for st in cfg['steps']:
 sd=out/st['module'];sd.mkdir()
 t0=time.monotonic()
 with (sd/'stdout.log').open('w') as lg:
  r=subprocess.run(['/usr/bin/time','-v','-o',str(sd/'time.log'),'timeout',str(cfg.get('timeout',180)),*st['command']],cwd=base,env=env,stdout=lg,stderr=subprocess.STDOUT)
 dur=time.monotonic()-t0
 log=(sd/'stdout.log').read_text();tim=(sd/'time.log').read_text()
 rss=metric(tim,'Maximum resident set size')
 steps.append(dict(module=st['module'],exit_status=r.returncode,wall_seconds=dur,peak_rss_kib=rss,swaps=metric(tim,'Swaps'),errors=len([l for l in log.split('\n') if ': error' in l]),
   source_sha256=hashlib.sha256((base/st['source']).read_bytes()).hexdigest(),
   olean_sha256=(hashlib.sha256(pathlib.Path(st['olean']).read_bytes()).hexdigest() if pathlib.Path(st['olean']).exists() else None),
   print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log)))
 worst=max(worst,int(rss or 0))
 if r.returncode!=0: rc=r.returncode;break
receipt={**{k:v for k,v in cfg.items() if k!='steps'},'steps':steps,'exit_status':rc,'wall_seconds':time.monotonic()-t_all,'peak_rss_kib':worst,'swaps':max(int(s['swaps'] or 0) for s in steps),'cgroup':str(rel),'limits':limits,'cgroup_memory_peak_bytes':(rel/'memory.peak').read_text().strip(),'source_hashes':{f:hashlib.sha256((out/'sources'/f).read_bytes()).hexdigest() for f in cfg['sources']}}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}))
sys.exit(rc)
