#!/usr/bin/env python3
"""One independently capped tiny extraction, with source/tool preflight+go."""
import hashlib,json,os,pathlib,subprocess,sys,time,threading
import Port20ALLOC_gate as gate
B=pathlib.Path(__file__).resolve().parent
cfg=json.loads((B/sys.argv[1]).read_text()); out=B/cfg['attempt'];out.mkdir(exist_ok=False)
cg=pathlib.Path('/sys/fs/cgroup')/next(l[3:].strip().lstrip('/') for l in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0::'))
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':'1610612736','memory.max':'2147483648','memory.swap.max':'0','pids.max':'64'},limits
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def verify():
    for p,h in cfg['input_hashes'].items(): assert sha(B/p)==h,p
    for p,h in cfg['tool_sysroot_hashes'].items(): assert sha(p)==h,p
verify()
admission=gate.snapshot();(out/'admission-in-scope.json').write_text(json.dumps(admission,indent=2)+'\n')
assert admission['admitted'], 'in-scope admission denied; no compiler launched'
stop=threading.Event(); metrics={'peak_aggregate_rss_bytes':0,'peak_observed_swap_bytes':0}
def monitor():
    while not stop.is_set():
        rss=swap=0
        for pid in (cg/'cgroup.procs').read_text().split():
            try:
                status=dict(l.split(':',1) for l in pathlib.Path('/proc',pid,'status').read_text().splitlines() if ':' in l)
                rss+=int(status.get('VmRSS','0 kB').split()[0])*1024
                swap+=int(status.get('VmSwap','0 kB').split()[0])*1024
            except FileNotFoundError: pass # telemetry only, not admission
        metrics['peak_aggregate_rss_bytes']=max(metrics['peak_aggregate_rss_bytes'],rss)
        metrics['peak_observed_swap_bytes']=max(metrics['peak_observed_swap_bytes'],swap)
        stop.wait(.1)
t=threading.Thread(target=monitor);t.start(); env=os.environ.copy();env.update(cfg['env'])
start=time.monotonic()
with (out/'stdout.log').open('w') as log:
    r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),'timeout','180',*cfg['command']],cwd=B,env=env,stdout=log,stderr=subprocess.STDOUT)
wall=time.monotonic()-start;stop.set();t.join(); verify()
receipt={**cfg,'exit_status':r.returncode,'wall_seconds':wall,'limits':limits,'cgroup':str(cg),
         'cgroup_memory_peak_bytes':int((cg/'memory.peak').read_text()),
         'cgroup_swap_current_bytes':int((cg/'memory.swap.current').read_text()),
         'cgroup_memory_events':(cg/'memory.events').read_text(),**metrics,
         'time_full':(out/'time.log').read_text(),'print_axioms':'N/A: native extraction; no Lean theorem'}
artifacts={}
for folder in ['Port20ALLOC-generated']:
    for p in (B/folder).rglob('*'):
        if p.is_file(): artifacts[str(p.relative_to(B))]=dict(sha256=sha(p),bytes=p.stat().st_size)
for p in B.glob('*.llbc'):artifacts[p.name]=dict(sha256=sha(p),bytes=p.stat().st_size)
receipt['artifacts']=artifacts
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['attempt','exit_status','wall_seconds','peak_aggregate_rss_bytes','cgroup_memory_peak_bytes','peak_observed_swap_bytes']}))
sys.exit(r.returncode)
