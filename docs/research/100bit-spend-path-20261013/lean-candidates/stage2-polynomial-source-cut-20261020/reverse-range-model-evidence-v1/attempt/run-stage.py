from pathlib import Path
import hashlib, json, os, subprocess, sys, time
w=Path(__file__).resolve().parent
c=json.loads((w/'config.json').read_text())
assert sys.argv[1]=='proof'
env=dict(os.environ);env['LEAN_PATH']=':'.join([str(w/'objects'),*c['lean_path']])
src=w/'sources/CurrentWideReverseRangeFoldModelV1.lean';obj=w/'objects/CurrentWideReverseRangeFoldModelV1.olean'
start=time.monotonic();cmd=['/usr/bin/time','-v','-o',str(w/'evidence-time.log'),c['lean'],'-o',str(obj),str(src)]
print('COMMAND '+json.dumps(cmd),flush=True)
p=subprocess.run(cmd,env=env,stdout=open(w/'lean.log','w'),stderr=subprocess.STDOUT)
wall=time.monotonic()-start
cg=None
for line in Path('/proc/self/cgroup').read_text().splitlines():
    if line.startswith('0::'): cg=Path('/sys/fs/cgroup')/line.split('::',1)[1].lstrip('/')
metrics={'exit_status':p.returncode,'wall_seconds':wall,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if obj.exists() else None,'command':cmd}
if cg and (cg/'memory.peak').exists(): metrics.update(scope_memory_peak_bytes=int((cg/'memory.peak').read_text()),scope_swap_current=int((cg/'memory.swap.current').read_text()),memory_events=(cg/'memory.events').read_text())
(w/'receipt.json').write_text(json.dumps(metrics,indent=2)+'\n')
print((w/'lean.log').read_text(),end='');print('RECEIPT '+json.dumps(metrics),flush=True)
raise SystemExit(p.returncode)
