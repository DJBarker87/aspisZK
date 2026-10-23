from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
W=Path(__file__).resolve().parent
phase,attempt=sys.argv[1:3]
assert phase=='readonly'
cfg=json.loads((W/'runtime-command.json').read_text())
out=W/'runs'/phase/attempt
out.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name,pin in cfg['input_pins'].items():assert sha(pin['path'])==pin['sha256'],name
CG=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().removeprefix('0::').lstrip('/')
limits={k:(CG/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max']}
assert limits=={'memory.high':str(512*1024**2),'memory.max':str(1024**3),'memory.swap.max':'0'}
env=dict(os.environ);env.update(cfg['env']);os.umask(0o077)
argv=cfg['argv'][:-1]+[str(out/'runtime')]
(out/'command.json').write_text(json.dumps({**cfg,'argv':argv,'limits':limits,'runner_sha256':sha(__file__)},indent=2)+'\n')
before=(CG/'memory.events').read_text();start=time.monotonic()
with (out/'stdout.log').open('x') as log:
 r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),*argv],cwd=W,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=180)
timing=(out/'time.log').read_text();rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
receipt={'exit_status':r.returncode,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(rss[1]) if rss else None,'scope_peak_bytes':int((CG/'memory.peak').read_text()),'scope_swap_bytes':int((CG/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(CG/'memory.events').read_text(),'limits':limits,'input_pins':cfg['input_pins'],'command_sha256':sha(out/'command.json')}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
if r.returncode:raise SystemExit(r.returncode)
summaries={}
for folder in ['readonly-buffer-stage1-runtime','readonly-metadata-runtime']:
 p=out/'runtime/after'/folder/'summary.json'
 if not p.exists():
  matches=list((out/'runtime').rglob(folder+'/summary.json'));assert len(matches)==1,matches;p=matches[0]
 summaries[folder]={'path':str(p),'sha256':sha(p),'summary':json.loads(p.read_text())}
(out/'readonly-summaries.json').write_text(json.dumps(summaries,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
